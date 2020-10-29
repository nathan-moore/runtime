// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

//

#include "jitpch.h"
#include "rangecheck.h"

// Max stack depth (path length) in walking the UD chain.
static const int MAX_SEARCH_DEPTH = 100;

// Max nodes to visit in the UD chain for the current method being compiled.
static const int MAX_VISIT_BUDGET = 8192;

// RangeCheck constructor.
RangeCheck::RangeCheck(Compiler* pCompiler)
    : m_pRangeMap(nullptr)
#ifdef DEBUG
    , m_fMappedDefs(false)
    , m_pDefTable(nullptr)
#endif
    , m_pCompiler(pCompiler)
    , m_alloc(pCompiler->getAllocator(CMK_RangeCheck))
    , m_nVisitBudget(MAX_VISIT_BUDGET)
{
    m_pPath = new (m_alloc) SearchPath(m_alloc);
}

bool RangeCheck::IsOverBudget()
{
    return (m_nVisitBudget <= 0);
}
// Get the range map in which computed ranges are cached.
RangeCheck::RangeMap* RangeCheck::GetRangeMap()
{
    if (m_pRangeMap == nullptr)
    {
        m_pRangeMap = new (m_alloc) RangeMap(m_alloc);
    }
    return m_pRangeMap;
}

// Get the overflow map in which computed overflows are cached.
RangeCheck::OverflowMap* RangeCheck::GetOverflowMap()
{
    if (m_pOverflowMap == nullptr)
    {
        m_pOverflowMap = new (m_alloc) OverflowMap(m_alloc);
    }
    return m_pOverflowMap;
}

// Get the length of the array vn, if it is new.
int RangeCheck::GetArrLength(ValueNum vn)
{
    ValueNum arrRefVN = m_pCompiler->vnStore->GetArrForLenVn(vn);
    return m_pCompiler->vnStore->GetNewArrSize(arrRefVN);
}

//------------------------------------------------------------------------
// BetweenBounds: Check if the computed range is within bounds
//
// Arguments:
//    Range - the range to check if in bounds
//    upper - the array length vn
//    arrSize - the length of the array if known, or <= 0
//
// Return Value:
//    True iff range is between [0 and vn - 1] or [0, arrSize - 1]
//
// notes:
//    This function assumes that the lower range is resolved and upper range is symbolic as in an
//    increasing loop.
//
// TODO-CQ: This is not general enough.
//
bool RangeCheck::BetweenBounds(Range& range, GenTree* upper, int arrSize)
{
#ifdef DEBUG
    if (m_pCompiler->verbose)
    {
        printf("%s BetweenBounds <%d, ", range.ToString(m_pCompiler->getAllocatorDebugOnly()), 0);
        Compiler::printTreeID(upper);
        printf(">\n");
    }
#endif // DEBUG

    ValueNumStore* vnStore = m_pCompiler->vnStore;

    // Get the VN for the upper limit.
    ValueNum uLimitVN = vnStore->VNConservativeNormalValue(upper->gtVNPair);

#ifdef DEBUG
    JITDUMP(FMT_VN " upper bound is: ", uLimitVN);
    if (m_pCompiler->verbose)
    {
        vnStore->vnDump(m_pCompiler, uLimitVN);
    }
    JITDUMP("\n");
#endif

    if ((arrSize <= 0) && !vnStore->IsVNCheckedBound(uLimitVN))
    {
        // If we don't know the array size and the upper limit is not known, then bail.
        return false;
    }

    JITDUMP("Array size is: %d\n", arrSize);

    // Upper limit: len + ucns (upper limit constant).
    if (range.UpperLimit().IsBinOpArray())
    {
        if (range.UpperLimit().vn != uLimitVN)
        {
            return false;
        }

        int ucns = range.UpperLimit().GetConstant();

        // Upper limit: Len + [0..n]
        if (ucns >= 0)
        {
            return false;
        }

        // Since upper limit is bounded by the array, return true if lower bound is good.
        if (range.LowerLimit().IsConstant() && range.LowerLimit().GetConstant() >= 0)
        {
            return true;
        }

        // Check if we have the array size allocated by new.
        if (arrSize <= 0)
        {
            return false;
        }

        // At this point,
        // upper limit = len + ucns. ucns < 0
        // lower limit = len + lcns.
        if (range.LowerLimit().IsBinOpArray())
        {
            int lcns = range.LowerLimit().GetConstant();
            if (lcns >= 0 || -lcns > arrSize)
            {
                return false;
            }
            return (range.LowerLimit().vn == uLimitVN && lcns <= ucns);
        }
    }
    // If upper limit is constant
    else if (range.UpperLimit().IsConstant())
    {
        if (arrSize <= 0)
        {
            return false;
        }
        int ucns = range.UpperLimit().GetConstant();
        if (ucns >= arrSize)
        {
            return false;
        }
        if (range.LowerLimit().IsConstant())
        {
            int lcns = range.LowerLimit().GetConstant();
            // Make sure lcns < ucns which is already less than arrSize.
            return (lcns >= 0 && lcns <= ucns);
        }
        if (range.LowerLimit().IsBinOpArray())
        {
            int lcns = range.LowerLimit().GetConstant();
            // len + lcns, make sure we don't subtract too much from len.
            if (lcns >= 0 || -lcns > arrSize)
            {
                return false;
            }
            // Make sure a.len + lcns <= ucns.
            return (range.LowerLimit().vn == uLimitVN && (arrSize + lcns) <= ucns);
        }
    }

    return false;
}

class NodeWidener : public DefinitionIterator<NodeWidener>
{
public:
    NodeWidener(RangeCheck* rangeCheck)
        : DefinitionIterator<NodeWidener>(rangeCheck)
    {}

    void WalkNodeRange(GenTree* node, const Range& range DEBUGARG(int indent))
    {
        Range newRange(Limit::keUnknown);
        if (!skipRecursivePhis) // we want to widen when not skipping recursive phis for this walker
        {
            Range oldRange = m_pRangeCheck->GetRange(node DEBUGARG(indent));

            if (!node->OperIs(GT_PHI))
            {
                newRange = range;
            }
            else
            {
                RangeOps::CompareResults lower = RangeOps::CompareLimit(range.lLimit, oldRange.lLimit);
                RangeOps::CompareResults upper = RangeOps::CompareLimit(range.uLimit, oldRange.uLimit);

                if ((lower == RangeOps::CouldNotCompare) || (upper == RangeOps::CouldNotCompare))
                {
                    newRange = Range(Limit::keUnknown);
                }
                else
                {
                    newRange = oldRange;
                    if (lower == RangeOps::LessThen)
                    {
                        newRange.lLimit = Limit(Limit::keDependent);
                    }

                    if (upper == RangeOps::GreaterThen)
                    {
                        newRange.uLimit = Limit(Limit::keDependent);
                    }
                }
            }
        }
        else
        {
            newRange = range;
        }

        m_pRangeCheck->SetRange(node, newRange);
    }
};

class NodeNarrower : public DefinitionIterator<NodeNarrower>
{
public:
    NodeNarrower(RangeCheck* rangeCheck, BasicBlock* bb) 
        : DefinitionIterator<NodeNarrower>(rangeCheck)
    {
        basicBlocks->Push(bb);
    }

    void WalkNodeRange(GenTree* node, const Range& range DEBUGARG(int indent))
    {
        // TODO_Nathan: the range within recursive loops should be correct due to merging assertions from top down, and
        // the range after loops should be right due to phis after recursive loops
        // I should make sure that there are test cases for both of these cases though.
        Range newRange = range;
        if (node->IsLocal() || node->OperIs(GT_PHI)) // TODO_Nathan: this is what it used. See if Phis are really necessary
        {
            m_pRangeCheck->MergeAssertion(basicBlocks->Top(), node, &newRange DEBUGARG(indent));
        }

        // set the range in case we improved a node upstream
        m_pRangeCheck->SetRange(node, newRange);
    }
};

void RangeCheck::OptimizeRangeCheck(BasicBlock* block, Statement* stmt, GenTree* treeParent)
{
    // Check if we are dealing with a bounds check node.
    if (treeParent->OperGet() != GT_COMMA)
    {
        return;
    }

    // If we are not looking at array bounds check, bail.
    GenTree* tree = treeParent->AsOp()->gtOp1;
    if (!tree->OperIsBoundsCheck())
    {
        return;
    }

    GenTreeBoundsChk* bndsChk = tree->AsBoundsChk();
    m_pCurBndsChk             = bndsChk;
    GenTree* treeIndex        = bndsChk->gtIndex;

    // Take care of constant index first, like a[2], for example.
    ValueNum idxVn    = m_pCompiler->vnStore->VNConservativeNormalValue(treeIndex->gtVNPair);
    ValueNum arrLenVn = m_pCompiler->vnStore->VNConservativeNormalValue(bndsChk->gtArrLen->gtVNPair);
    int      arrSize  = 0;

    if (m_pCompiler->vnStore->IsVNConstant(arrLenVn))
    {
        ssize_t  constVal  = -1;
        unsigned iconFlags = 0;

        if (m_pCompiler->optIsTreeKnownIntValue(true, bndsChk->gtArrLen, &constVal, &iconFlags))
        {
            arrSize = (int)constVal;
        }
    }
    else
#ifdef FEATURE_SIMD
        if (tree->gtOper != GT_SIMD_CHK
#ifdef FEATURE_HW_INTRINSICS
            && tree->gtOper != GT_HW_INTRINSIC_CHK
#endif // FEATURE_HW_INTRINSICS
            )
#endif // FEATURE_SIMD
    {
        arrSize = GetArrLength(arrLenVn);

        // if we can't find the array length, see if there
        // are any assertions about the array size we can use to get a minimum length
        if (arrSize <= 0)
        {
            JITDUMP("Looking for array size assertions for: " FMT_VN "\n", arrLenVn);
            Range arrLength = Range(Limit(Limit::keDependent));
            MergeEdgeAssertions(arrLenVn, block->bbAssertionIn, &arrLength);
            if (arrLength.lLimit.IsConstant())
            {
                arrSize = arrLength.lLimit.GetConstant();
            }
        }
    }

    JITDUMP("ArrSize for lengthVN:%03X = %d\n", arrLenVn, arrSize);
    if (m_pCompiler->vnStore->IsVNConstant(idxVn) && (arrSize > 0))
    {
        ssize_t  idxVal    = -1;
        unsigned iconFlags = 0;
        if (!m_pCompiler->optIsTreeKnownIntValue(true, treeIndex, &idxVal, &iconFlags))
        {
            return;
        }

        JITDUMP("[RangeCheck::OptimizeRangeCheck] Is index %d in <0, arrLenVn " FMT_VN " sz:%d>.\n", idxVal, arrLenVn,
                arrSize);
        if ((idxVal < arrSize) && (idxVal >= 0))
        {
            JITDUMP("Removing range check\n");
            m_pCompiler->optRemoveRangeCheck(treeParent, stmt);
            return;
        }
    }

    GetRangeMap()->RemoveAll(); // TODO: remove
    GetOverflowMap()->RemoveAll();
    m_pRangeMap->RemoveAll(); // TODO: remove

    NodeWidener widener(this);
    widener.SetSkipRecursivePhis(true);
    // Compute the range for this index.
    widener.StartWalk(treeIndex);

    if (widener.IsErrorState())
    {
        JITDUMP("Error in NodeWidener. Bailing removing range check\n");
        return;
    }

    // TODO_Nathan: this will double print?
    Range range = GetRange(treeIndex DEBUGARG(0));

    // In some cases we can get around unkown due to assertions/narrowing. We need a different mechanism to identify overflow
    // If upper or lower limit is found to be unknown, or it was found to
    // be unknown because of over budget or a deep search, then return early.
    /*if (range.UpperLimit().IsUnknown() || range.LowerLimit().IsUnknown())
    {
        // Note: If we had stack depth too deep in the GetRange call, we'd be
        // too deep even in the DoesOverflow call. So return early.
        return;
    }
    else*/ if (range.IsRecursive())
    {
        widener.SetSkipRecursivePhis(false); // TODO: JITDUMP
        widener.StartWalk(treeIndex);
        range = GetRange(treeIndex DEBUGARG(0));
        //assert(!range.IsRecursive());
        assert(!widener.IsErrorState() && "Should not error after initial walk succeeded");
    }

    JITDUMP("Range value %s\n", range.ToString(m_pCompiler->getAllocatorDebugOnly()));
    
    // TODO: narrowing
    NodeNarrower narrower(this, block);
    narrower.StartWalk(treeIndex);
    assert(!narrower.IsErrorState());

    range = GetRange(treeIndex DEBUGARG(0));
    if (range.UpperLimit().IsUnknown() || range.LowerLimit().IsUnknown())
    {
        JITDUMP("Not removing range check due to unkowns after lowering\n");
        return;
    }

    // TODO: enable overflow
    if (false && DoesOverflow(treeIndex))
    {
        JITDUMP("Method determined to overflow\n");
        return;
    }
    range = GetRange(treeIndex DEBUGARG(0));
    // Is the range between the lower and upper bound values.
    if (BetweenBounds(range, bndsChk->gtArrLen, arrSize))
    {
        JITDUMP("[RangeCheck::OptimizeRangeCheck] Between bounds\n");
        m_pCompiler->optRemoveRangeCheck(treeParent, stmt);
    }
    return;
}

// Given a lclvar use, try to find the lclvar's defining assignment and its containing block.
LclSsaVarDsc* RangeCheck::GetSsaDefAsg(GenTreeLclVarCommon* lclUse)
{
    unsigned ssaNum = lclUse->GetSsaNum();

    if (ssaNum == SsaConfig::RESERVED_SSA_NUM)
    {
        return nullptr;
    }

    LclVarDsc* varDsc = m_pCompiler->lvaGetDesc(lclUse);
    if (varDsc->CanBeReplacedWithItsField(m_pCompiler))
    {
        varDsc = m_pCompiler->lvaGetDesc(varDsc->lvFieldLclStart);
    }
    LclSsaVarDsc* ssaDef = varDsc->GetPerSsaData(ssaNum);

    // RangeCheck does not care about uninitialized variables.
    if (ssaDef->GetAssignment() == nullptr)
    {
        return nullptr;
    }

    // RangeCheck does not understand definitions generated by LCL_FLD nodes
    // nor definitions generated by indirect stores to local variables.
    if (!ssaDef->GetAssignment()->gtGetOp1()->OperIs(GT_LCL_VAR))
    {
        return nullptr;
    }

#ifdef DEBUG
    Location* loc = GetDef(lclUse);
    assert(loc != nullptr);
    assert(loc->parent == ssaDef->GetAssignment());
    assert(loc->block == ssaDef->GetBlock());
#endif

    return ssaDef;
}

#ifdef DEBUG
UINT64 RangeCheck::HashCode(unsigned lclNum, unsigned ssaNum)
{
    LclVarDsc* varDsc = m_pCompiler->lvaGetDesc(lclNum);
    if (varDsc->CanBeReplacedWithItsField(m_pCompiler))
    {
        lclNum = varDsc->lvFieldLclStart;
    }
    assert(ssaNum != SsaConfig::RESERVED_SSA_NUM);
    return UINT64(lclNum) << 32 | ssaNum;
}

// Get the def location of a given variable.
RangeCheck::Location* RangeCheck::GetDef(unsigned lclNum, unsigned ssaNum)
{
    Location* loc = nullptr;
    if (ssaNum == SsaConfig::RESERVED_SSA_NUM)
    {
        return nullptr;
    }
    if (!m_fMappedDefs)
    {
        MapMethodDefs();
    }
    // No defs.
    if (m_pDefTable == nullptr)
    {
        return nullptr;
    }
    m_pDefTable->Lookup(HashCode(lclNum, ssaNum), &loc);
    return loc;
}

RangeCheck::Location* RangeCheck::GetDef(GenTreeLclVarCommon* lcl)
{
    unsigned lclNum = lcl->GetLclNum();
    return GetDef(lclNum, lcl->GetSsaNum());
}

// Add the def location to the hash table.
void RangeCheck::SetDef(UINT64 hash, Location* loc)
{
    if (m_pDefTable == nullptr)
    {
        m_pDefTable = new (m_alloc) VarToLocMap(m_alloc);
    }
#ifdef DEBUG
    Location* loc2;
    if (m_pDefTable->Lookup(hash, &loc2))
    {
        JITDUMP("Already have " FMT_BB ", " FMT_STMT ", [%06d] for hash => %0I64X", loc2->block->bbNum,
                loc2->stmt->GetID(), Compiler::dspTreeID(loc2->tree), hash);
        assert(false);
    }
#endif
    m_pDefTable->Set(hash, loc);
}
#endif

//------------------------------------------------------------------------
// MergeEdgeAssertions: Merge assertions on the edge flowing into the block about a variable
//
// Arguments:
//    GenTreeLclVarCommon - the variable to look for assertions for
//    assertions - the assertions to use
//    pRange - the range to tighten with assertions
//
void RangeCheck::MergeEdgeAssertions(GenTreeLclVarCommon* lcl, ASSERT_VALARG_TP assertions, Range* pRange)
{
    if (lcl->GetSsaNum() == SsaConfig::RESERVED_SSA_NUM)
    {
        return;
    }

    LclVarDsc* varDsc = m_pCompiler->lvaGetDesc(lcl);
    if (varDsc->CanBeReplacedWithItsField(m_pCompiler))
    {
        varDsc = m_pCompiler->lvaGetDesc(varDsc->lvFieldLclStart);
    }
    LclSsaVarDsc* ssaData     = varDsc->GetPerSsaData(lcl->GetSsaNum());
    ValueNum      normalLclVN = m_pCompiler->vnStore->VNConservativeNormalValue(ssaData->m_vnPair);
    MergeEdgeAssertions(normalLclVN, assertions, pRange);
}

//------------------------------------------------------------------------
// MergeEdgeAssertions: Merge assertions on the edge flowing into the block about a variable
//
// Arguments:
//    normalLclVN - the value number to look for assertions for
//    assertions - the assertions to use
//    pRange - the range to tighten with assertions
//
void RangeCheck::MergeEdgeAssertions(ValueNum normalLclVN, ASSERT_VALARG_TP assertions, Range* pRange)
{
    if (BitVecOps::IsEmpty(m_pCompiler->apTraits, assertions))
    {
        return;
    }

    if (normalLclVN == ValueNumStore::NoVN)
    {
        return;
    }

    // Walk through the "assertions" to check if the apply.
    BitVecOps::Iter iter(m_pCompiler->apTraits, assertions);
    unsigned        index = 0;
    while (iter.NextElem(&index))
    {
        AssertionIndex assertionIndex = GetAssertionIndex(index);

        Compiler::AssertionDsc* curAssertion = m_pCompiler->optGetAssertion(assertionIndex);

        Limit      limit(Limit::keUndef);
        genTreeOps cmpOper             = GT_NONE;
        bool       isConstantAssertion = false;

        // Current assertion is of the form (i < len - cns) != 0
        if (curAssertion->IsCheckedBoundArithBound())
        {
            ValueNumStore::CompareCheckedBoundArithInfo info;

            // Get i, len, cns and < as "info."
            m_pCompiler->vnStore->GetCompareCheckedBoundArithInfo(curAssertion->op1.vn, &info);

            // If we don't have the same variable we are comparing against, bail.
            if (normalLclVN != info.cmpOp)
            {
                continue;
            }

            if ((info.arrOper != GT_ADD) && (info.arrOper != GT_SUB))
            {
                continue;
            }

            // If the operand that operates on the bound is not constant, then done.
            if (!m_pCompiler->vnStore->IsVNInt32Constant(info.arrOp))
            {
                continue;
            }

            int cons = m_pCompiler->vnStore->ConstantValue<int>(info.arrOp);
            limit    = Limit(Limit::keBinOpArray, info.vnBound, info.arrOper == GT_SUB ? -cons : cons);
            cmpOper  = (genTreeOps)info.cmpOper;
        }
        // Current assertion is of the form (i < len) != 0
        else if (curAssertion->IsCheckedBoundBound())
        {
            ValueNumStore::CompareCheckedBoundArithInfo info;

            // Get the info as "i", "<" and "len"
            m_pCompiler->vnStore->GetCompareCheckedBound(curAssertion->op1.vn, &info);

            // If we don't have the same variable we are comparing against, bail.
            if (normalLclVN == info.cmpOp)
            {
                cmpOper = (genTreeOps)info.cmpOper;
                limit   = Limit(Limit::keBinOpArray, info.vnBound, 0);
            }
            else if (normalLclVN == info.vnBound)
            {
                cmpOper = GenTree::SwapRelop((genTreeOps)info.cmpOper);
                limit   = Limit(Limit::keBinOpArray, info.cmpOp, 0);
            }
            else
            {
                continue;
            }
        }
        // Current assertion is of the form (i < 100) != 0
        else if (curAssertion->IsConstantBound())
        {
            ValueNumStore::ConstantBoundInfo info;

            // Get the info as "i", "<" and "100"
            m_pCompiler->vnStore->GetConstantBoundInfo(curAssertion->op1.vn, &info);

            // If we don't have the same variable we are comparing against, bail.
            if (normalLclVN != info.cmpOpVN)
            {
                continue;
            }

            limit   = Limit(Limit::keConstant, info.constVal);
            cmpOper = (genTreeOps)info.cmpOper;
        }
        // Current assertion is of the form i == 100
        else if (curAssertion->IsConstantInt32Assertion() && (curAssertion->op2.vn != 0)) // TODO_Nathan: ?
        {
            if (curAssertion->op1.vn != normalLclVN)
            {
                continue;
            }

            int cnstLimit = m_pCompiler->vnStore->CoercedConstantValue<int>(curAssertion->op2.vn);

            if ((cnstLimit == 0) && (curAssertion->assertionKind == Compiler::OAK_NOT_EQUAL) &&
                m_pCompiler->vnStore->IsVNCheckedBound(curAssertion->op1.vn))
            {
                // we have arr.Len != 0, so the length must be atleast one
                limit   = Limit(Limit::keConstant, 1);
                cmpOper = GT_GE;
            }
            else if (curAssertion->assertionKind == Compiler::OAK_EQUAL)
            {
                limit   = Limit(Limit::keConstant, cnstLimit);
                cmpOper = GT_EQ;
            }
            else
            {
                // We have a != assertion, but it doesn't tell us much about the interval. So just skip it.
                continue;
            }

            isConstantAssertion = true;
        }
        // Current assertion is not supported, ignore it
        else
        {
            continue;
        }

        assert(limit.IsBinOpArray() || limit.IsConstant());

        // Make sure the assertion is of the form != 0 or == 0 if it isn't a constant assertion.
        if (!isConstantAssertion && (curAssertion->op2.vn != m_pCompiler->vnStore->VNZeroForType(TYP_INT)))
        {
            continue;
        }
#ifdef DEBUG
        if (m_pCompiler->verbose)
        {
            m_pCompiler->optPrintAssertion(curAssertion, assertionIndex);
        }
#endif

        // Limits are sometimes made with the form vn + constant, where vn is a known constant
        // see if we can simplify this to just a constant
        if (limit.IsBinOpArray() && m_pCompiler->vnStore->IsVNInt32Constant(limit.vn))
        {
            Limit tempLimit = Limit(Limit::keConstant, m_pCompiler->vnStore->ConstantValue<int>(limit.vn));
            if (tempLimit.AddConstant(limit.cns))
            {
                limit = tempLimit;
            }
        }

        ValueNum arrLenVN = m_pCompiler->vnStore->VNConservativeNormalValue(m_pCurBndsChk->gtArrLen->gtVNPair);

        if (m_pCompiler->vnStore->IsVNConstant(arrLenVN))
        {
            // Set arrLenVN to NoVN; this will make it match the "vn" recorded on
            // constant limits (where we explicitly track the constant and don't
            // redundantly store its VN in the "vn" field).
            arrLenVN = ValueNumStore::NoVN;
        }

        // During assertion prop we add assertions of the form:
        //
        //      (i < length) == 0
        //      (i < length) != 0
        //      (i < 100) == 0
        //      (i < 100) != 0
        //      i == 100
        //
        // At this point, we have detected that either op1.vn is (i < length) or (i < length + cns) or
        // (i < 100) and the op2.vn is 0 or that op1.vn is i and op2.vn is a known constant.
        //
        // Now, let us check if we are == 0 (i.e., op1 assertion is false) or != 0 (op1 assertion
        // is true.).
        //
        // If we have a non-constant assertion of the form == 0 (i.e., equals false), then reverse relop.
        // The relop has to be reversed because we have: (i < length) is false which is the same
        // as (i >= length).
        if ((curAssertion->assertionKind == Compiler::OAK_EQUAL) && !isConstantAssertion)
        {
            cmpOper = GenTree::ReverseRelop(cmpOper);
        }

        assert(cmpOper != GT_NONE);

        // Bounds are inclusive, so add -1 for upper bound when "<". But make sure we won't underflow.
        if (cmpOper == GT_LT && !limit.AddConstant(-1))
        {
            continue;
        }
        // Bounds are inclusive, so add +1 for lower bound when ">". But make sure we won't overflow.
        if (cmpOper == GT_GT && !limit.AddConstant(1))
        {
            continue;
        }

        // Doesn't tighten the current bound. So skip.
        if (pRange->uLimit.IsConstant() && limit.vn != arrLenVN)
        {
            continue;
        }

        // Check if the incoming limit from assertions tightens the existing upper limit.
        if (pRange->uLimit.IsBinOpArray() && (pRange->uLimit.vn == arrLenVN))
        {
            // We have checked the current range's (pRange's) upper limit is either of the form:
            //      length + cns
            //      and length == the bndsChkCandidate's arrLen
            //
            // We want to check if the incoming limit tightens the bound, and for that
            // we need to make sure that incoming limit is also on the same length (or
            // length + cns) and not some other length.

            if (limit.vn != arrLenVN)
            {
                JITDUMP("Array length VN did not match arrLen=" FMT_VN ", limit=" FMT_VN "\n", arrLenVN, limit.vn);
                continue;
            }

            int curCns = pRange->uLimit.cns;
            int limCns = (limit.IsBinOpArray()) ? limit.cns : 0;

            // Incoming limit doesn't tighten the existing upper limit.
            if (limCns >= curCns)
            {
                JITDUMP("Bound limit %d doesn't tighten current bound %d\n", limCns, curCns);
                continue;
            }
        }
        else
        {
            // Current range's upper bound is not "length + cns" and the
            // incoming limit is not on the same length as the bounds check candidate.
            // So we could skip this assertion. But in cases, of Dependent or Unknown
            // type of upper limit, the incoming assertion still tightens the upper
            // bound to a saner value. So do not skip the assertion.
        }

        // cmpOp (loop index i) cmpOper len +/- cns
        switch (cmpOper)
        {
            case GT_LT:
            case GT_LE:
                pRange->uLimit = limit;
                break;

            case GT_GT:
            case GT_GE:
                pRange->lLimit = limit;
                break;

            case GT_EQ:
                pRange->uLimit = limit;
                pRange->lLimit = limit;
                break;

            default:
                // All other 'cmpOper' kinds leave lLimit/uLimit unchanged
                break;
        }
        JITDUMP("The range after edge merging:");
        JITDUMP(pRange->ToString(m_pCompiler->getAllocatorDebugOnly()));
        JITDUMP("\n");
    }
}

// Merge assertions from the pred edges of the block, i.e., check for any assertions about "op's" value numbers for phi
// arguments. If not a phi argument, check if we have assertions about local variables.
void RangeCheck::MergeAssertion(BasicBlock* block, GenTree* op, Range* pRange DEBUGARG(int indent))
{
    JITDUMP("Merging assertions from pred edges of " FMT_BB " for op [%06d] " FMT_VN "\n", block->bbNum,
            Compiler::dspTreeID(op), m_pCompiler->vnStore->VNConservativeNormalValue(op->gtVNPair));
    ASSERT_TP assertions = BitVecOps::UninitVal();

    // If we have a phi arg, we can get to the block from it and use its assertion out.
    if (op->gtOper == GT_PHI_ARG)
    {
        GenTreePhiArg* arg  = (GenTreePhiArg*)op;
        BasicBlock*    pred = arg->gtPredBB;
        if (pred->bbFallsThrough() && pred->bbNext == block)
        {
            assertions = pred->bbAssertionOut;
            JITDUMP("Merge assertions from pred " FMT_BB " edge: %s\n", pred->bbNum,
                    BitVecOps::ToString(m_pCompiler->apTraits, assertions));
        }
        else if ((pred->bbJumpKind == BBJ_COND || pred->bbJumpKind == BBJ_ALWAYS) && pred->bbJumpDest == block)
        {
            if (m_pCompiler->bbJtrueAssertionOut != nullptr)
            {
                assertions = m_pCompiler->bbJtrueAssertionOut[pred->bbNum];
                JITDUMP("Merge assertions from pred " FMT_BB " JTrue edge: %s\n", pred->bbNum,
                        BitVecOps::ToString(m_pCompiler->apTraits, assertions));
            }
        }
    }
    // Get assertions from bbAssertionIn.
    else if (op->IsLocal())
    {
        assertions = block->bbAssertionIn;
    }

    if (!BitVecOps::MayBeUninit(assertions) && (m_pCompiler->GetAssertionCount() > 0))
    {
        // Perform the merge step to fine tune the range value.
        MergeEdgeAssertions(op->AsLclVarCommon(), assertions, pRange);
    }
}

// Compute the range for a binary operation.
Range RangeCheck::ComputeRangeForBinOp(GenTreeOp* binop DEBUGARG(int indent))
{
    assert(binop->OperIs(GT_ADD, GT_AND, GT_RSH, GT_LSH, GT_UMOD));

    GenTree* op1 = binop->gtGetOp1();
    GenTree* op2 = binop->gtGetOp2();

    if (binop->OperIs(GT_AND, GT_RSH, GT_LSH, GT_UMOD))
    {
        if (!op2->IsIntCnsFitsInI32())
        {
            // only cns is supported for op2 at the moment for &,%,<<,>> operators
            return Range(Limit::keUnknown);
        }

        int icon = -1;
        if (binop->OperIs(GT_AND))
        {
            // x & cns -> [0..cns]
            icon = static_cast<int>(op2->AsIntCon()->IconValue());
        }
        else if (binop->OperIs(GT_UMOD))
        {
            // x % cns -> [0..cns-1]
            icon = static_cast<int>(op2->AsIntCon()->IconValue()) - 1;
        }
        else if (binop->OperIs(GT_RSH, GT_LSH) && op1->OperIs(GT_AND) && op1->AsOp()->gtGetOp2()->IsIntCnsFitsInI32())
        {
            // (x & cns1) >> cns2 -> [0..cns1>>cns2]
            int icon1 = static_cast<int>(op1->AsOp()->gtGetOp2()->AsIntCon()->IconValue());
            int icon2 = static_cast<int>(op2->AsIntCon()->IconValue());
            if ((icon1 >= 0) && (icon2 >= 0) && (icon2 < 32))
            {
                icon = binop->OperIs(GT_RSH) ? (icon1 >> icon2) : (icon1 << icon2);
            }
        }

        if (icon < 0)
        {
            return Range(Limit::keUnknown);
        }
        Range range(Limit(Limit::keConstant, 0), Limit(Limit::keConstant, icon));
        JITDUMP("Limit range to %s\n", range.ToString(m_pCompiler->getAllocatorDebugOnly()));
        return range;
    }

    // other operators are expected to be handled above.
    assert(binop->OperIs(GT_ADD));

    // Check if the range value is already cached.
    // If we already have the op in the path, then, just rely on assertions, else
    // find the range.
    // TODO_Nathan: Update comment
    Range op1Range = GetRange(op1 DEBUGARG(indent));

    // If we already have the op in the path, then, just rely on assertions, else
    // find the range.
    // TODO_Nathan: update comment
    Range op2Range = GetRange(op2 DEBUGARG(indent));

    Range r = RangeOps::Add(op1Range, op2Range);
    JITDUMP("BinOp add ranges %s %s = %s\n", op1Range.ToString(m_pCompiler->getAllocatorDebugOnly()),
            op2Range.ToString(m_pCompiler->getAllocatorDebugOnly()), r.ToString(m_pCompiler->getAllocatorDebugOnly()));
    return r;
}

// Compute the range for a local var definition.
Range RangeCheck::ComputeRangeForLocalDef(GenTreeLclVarCommon* lcl
                                          DEBUGARG(int indent))
{
    LclSsaVarDsc* ssaDef = GetSsaDefAsg(lcl);
    if (ssaDef == nullptr)
    {
        return Range(Limit(Limit::keUnknown));
    }
#ifdef DEBUG
    if (m_pCompiler->verbose)
    {
        JITDUMP("----------------------------------------------------\n");
        m_pCompiler->gtDispTree(ssaDef->GetAssignment());
        JITDUMP("----------------------------------------------------\n");
    }
#endif
    // TODO_Nathan: shouldn't be necessary
    Range range = GetRange(ssaDef->GetAssignment()->gtGetOp2() DEBUGARG(indent));
    /*
    if (!BitVecOps::MayBeUninit(block->bbAssertionIn) && (m_pCompiler->GetAssertionCount() > 0))
    {
        JITDUMP("Merge assertions from " FMT_BB ":%s for assignment about [%06d]\n", block->bbNum,
                BitVecOps::ToString(m_pCompiler->apTraits, block->bbAssertionIn),
                Compiler::dspTreeID(ssaDef->GetAssignment()->gtGetOp1()));
        // TODO_Nathan: Edge Assertions
        // MergeEdgeAssertions(ssaDef->GetAssignment()->gtGetOp1()->AsLclVarCommon(), block->bbAssertionIn, &range);
        JITDUMP("done merging\n");
    }*/
    return range;
}

Range RangeCheck::MergePhi(GenTree* expr, bool skipRecursivePhis DEBUGARG(int indent))
{
    Range range = Limit(Limit::keUndef);
    for (GenTreePhi::Use& use : expr->AsPhi()->Uses())
    {
        Range argRange = GetRange(use.GetNode() DEBUGARG(indent));

        // TODO_Nathan: currently we use Dependent on recursive phis. It may make sense to use a special 
        // type
        // We don't skip recursive phis if they have actual data in them
        if (skipRecursivePhis && argRange.IsRecursive() && argRange.lLimit.IsDependent() && argRange.uLimit.IsDependent())
        {
            JITDUMP("Skipping recursive phi use\n");
            range.SetIsRecursive(true);
            continue;
        }

        JITDUMP("Merging ranges %s %s:", range.ToString(m_pCompiler->getAllocatorDebugOnly()),
                argRange.ToString(m_pCompiler->getAllocatorDebugOnly()));
        assert(!argRange.LowerLimit().IsUndef());
        assert(!argRange.UpperLimit().IsUndef());
        range = RangeOps::Merge(range, argRange);
        JITDUMP("%s\n", range.ToString(m_pCompiler->getAllocatorDebugOnly()));
    }

    if (range.LowerLimit().IsUndef() || range.UpperLimit().IsUndef())
    {
        assert(range.IsRecursive());
        if (range.LowerLimit().IsUndef())
            range.lLimit = Limit::keDependent;
        
        if (range.UpperLimit().IsUndef())
            range.uLimit = Limit::keDependent;
    }

    return range;
}


// https://msdn.microsoft.com/en-us/windows/apps/hh285054.aspx
// CLR throws IDS_EE_ARRAY_DIMENSIONS_EXCEEDED if array length is > INT_MAX.
// new byte[INT_MAX]; still throws OutOfMemoryException on my system with 32 GB RAM.
// I believe practical limits are still smaller than this number.
#define ARRLEN_MAX (0x7FFFFFFF)

// Get the limit's maximum possible value, treating array length to be ARRLEN_MAX.
bool RangeCheck::GetLimitMax(Limit& limit, int* pMax)
{
    int& max1 = *pMax;
    switch (limit.type)
    {
        case Limit::keConstant:
            max1 = limit.GetConstant();
            break;

        case Limit::keBinOpArray:
        {
            int tmp = GetArrLength(limit.vn);
            if (tmp <= 0)
            {
                tmp = ARRLEN_MAX;
            }
            if (IntAddOverflows(tmp, limit.GetConstant()))
            {
                return false;
            }
            max1 = tmp + limit.GetConstant();
        }
        break;

        default:
            return false;
    }
    return true;
}

// Check if the arithmetic overflows.
bool RangeCheck::AddOverflows(Limit& limit1, Limit& limit2)
{
    int max1;
    if (!GetLimitMax(limit1, &max1))
    {
        return true;
    }

    int max2;
    if (!GetLimitMax(limit2, &max2))
    {
        return true;
    }

    return IntAddOverflows(max1, max2);
}

// Does the bin operation overflow.
bool RangeCheck::DoesBinOpOverflow(GenTreeOp* binop)
{
    GenTree* op1 = binop->gtGetOp1();
    GenTree* op2 = binop->gtGetOp2();

    if (!IsBeingWalked(op1) && DoesOverflow(op1))
    {
        return true;
    }

    if (!IsBeingWalked(op2) && DoesOverflow(op2))
    {
        return true;
    }

    //TODO_Nathan: Improve this (eg take poiner?)
    // Get the cached ranges of op1
    Range op1Range = Range(Limit::keUnknown);
    if (!GetRangeMap()->Lookup(op1, &op1Range))
    {
        return true;
    }
    // Get the cached ranges of op2
    Range op2Range = Range(Limit::keUnknown);
    if (!GetRangeMap()->Lookup(op2, &op2Range))
    {
        return true;
    }

    JITDUMP("Checking bin op overflow %s %s\n", op1Range.ToString(m_pCompiler->getAllocatorDebugOnly()),
            op2Range.ToString(m_pCompiler->getAllocatorDebugOnly()));

    if (!AddOverflows(op1Range.UpperLimit(), op2Range.UpperLimit()))
    {
        return false;
    }
    return true;
}

// Check if the var definition the rhs involves arithmetic that overflows.
bool RangeCheck::DoesVarDefOverflow(GenTreeLclVarCommon* lcl)
{
    LclSsaVarDsc* ssaDef = GetSsaDefAsg(lcl);
    return (ssaDef == nullptr) || DoesOverflow(ssaDef->GetAssignment()->gtGetOp2());
}

bool RangeCheck::DoesPhiOverflow(GenTree* expr)
{
    for (GenTreePhi::Use& use : expr->AsPhi()->Uses())
    {
        GenTree* arg = use.GetNode();
        if (IsBeingWalked(arg))
        {
            continue;
        }
        if (DoesOverflow(arg))
        {
            return true;
        }
    }
    return false;
}

bool RangeCheck::DoesOverflow(GenTree* expr)
{
    //TODO_Nathan: improve
    bool overflows = false;
    if (!GetOverflowMap()->Lookup(expr, &overflows))
    {
        overflows = ComputeDoesOverflow(expr);
    }
    return overflows;
}

bool RangeCheck::ComputeDoesOverflow(GenTree* expr)
{
    JITDUMP("Does overflow [%06d]?\n", Compiler::dspTreeID(expr));

    bool overflows = true;

    /*if (m_pSearchPath->GetCount() > MAX_SEARCH_DEPTH) // TODO_Nathan: fixme
    {
        overflows = true;
    }
    // If the definition chain resolves to a constant, it doesn't overflow.
    else */if (m_pCompiler->vnStore->IsVNConstant(expr->gtVNPair.GetConservative()))
    {
        overflows = false;
    }
    else if (expr->OperGet() == GT_IND)
    {
        overflows = false;
    }
    else if (expr->OperGet() == GT_COMMA)
    {
        overflows = ComputeDoesOverflow(expr->gtEffectiveVal());
    }
    // Check if the var def has rhs involving arithmetic that overflows.
    else if (expr->IsLocal())
    {
        overflows = DoesVarDefOverflow(expr->AsLclVarCommon());
    }
    // Check if add overflows.
    else if (expr->OperGet() == GT_ADD)
    {
        overflows = DoesBinOpOverflow(expr->AsOp());
    }
    // GT_AND, GT_UMOD, GT_LSH and GT_RSH don't overflow
    // Actually, GT_LSH can overflow so it depends on the analysis done in ComputeRangeForBinOp
    else if (expr->OperIs(GT_AND, GT_RSH, GT_LSH, GT_UMOD))
    {
        overflows = false;
    }
    // Walk through phi arguments to check if phi arguments involve arithmetic that overflows.
    else if (expr->OperGet() == GT_PHI)
    {
        overflows = DoesPhiOverflow(expr);
    }
    GetOverflowMap()->Set(expr, overflows, OverflowMap::Overwrite);
    JITDUMP("[%06d] %s\n", Compiler::dspTreeID(expr), ((overflows) ? "overflows" : "does not overflow"));
    return overflows;
}


//------------------------------------------------------------------------
// ComputeRange: Compute the range recursively by asking for the range of each variable in the dependency chain.
//
// Arguments:
//   block - the block that contains `expr`;
//   expr - expression to compute the range for;
//   monIncreasing - true if `expr` is proven to be monotonically increasing;
//   indent - debug printing indent.
//
// Return value:
//   'expr' range as lower and upper limits.
//
// Notes:
//   eg.: c = a + b; ask range of "a" and "b" and add the results.
//   If the result cannot be determined i.e., the dependency chain does not terminate in a value,
//   but continues to loop, which will happen with phi nodes we end the looping by calling the
//   value as "dependent" (dep).
//   If the loop is proven to be "monIncreasing", then make liberal decisions for the lower bound
//   while merging phi node. eg.: merge((0, dep), (dep, dep)) = (0, dep),
//   merge((0, 1), (dep, dep)) = (0, dep), merge((0, 5), (dep, 10)) = (0, 10).
//
Range RangeCheck::ComputeRange(GenTree* expr, bool skipRecursivePhis DEBUGARG(int indent))
{
    //TODO_Nathan: FIXME BB
    Range range      = Limit(Limit::keUndef);

    ValueNum vn = m_pCompiler->vnStore->VNConservativeNormalValue(expr->gtVNPair);

    // If we just added 'expr' in the current search path, then reduce the budget.
    /*if (newlyAdded) //TODO: budget
    {
        // Assert that we are not re-entrant for a node which has been
        // visited and resolved before and not currently on the search path.
        noway_assert(!GetRangeMap()->Lookup(expr));
        m_nVisitBudget--;
    }*/
    // Prevent quadratic behavior.
    /*if (IsOverBudget())
    {
        // Set to unknown, since an Unknown range resolution, will stop further
        // searches. This is because anything that merges with Unknown will
        // yield Unknown. Unknown is lattice top.
        range = Range(Limit(Limit::keUnknown));
        JITDUMP("GetRange not tractable within max node visit budget.\n");
    }
    // Prevent unbounded recursion.
    else if (m_pSearchPath->GetCount() > MAX_SEARCH_DEPTH)
    {
        // Unknown is lattice top, anything that merges with Unknown will yield Unknown.
        range = Range(Limit(Limit::keUnknown));
        JITDUMP("GetRange not tractable within max stack depth.\n");
    }
    // TODO-CQ: The current implementation is reliant on integer storage types
    // for constants. It could use INT64. Still, representing ULONG constants
    // might require preserving the var_type whether it is a un/signed 64-bit.
    // JIT64 doesn't do anything for "long" either. No asm diffs.
    else */if (expr->TypeGet() == TYP_LONG || expr->TypeGet() == TYP_ULONG)
    {
        range = Range(Limit(Limit::keUnknown));
        JITDUMP("GetRange long or ulong, setting to unknown value.\n");
    }
    // If VN is constant return range as constant.
    else if (m_pCompiler->vnStore->IsVNConstant(vn))
    {
        range = (m_pCompiler->vnStore->TypeOfVN(vn) == TYP_INT)
                    ? Range(Limit(Limit::keConstant, m_pCompiler->vnStore->ConstantValue<int>(vn)))
                    : Limit(Limit::keUnknown);
    }
    // If local, find the definition from the def map and evaluate the range for rhs.
    else if (expr->IsLocal())
    {
        range = ComputeRangeForLocalDef(expr->AsLclVarCommon() DEBUGARG(indent + 1));
    }
    // compute the range for binary operation
    else if (expr->OperIs(GT_ADD, GT_AND, GT_RSH, GT_LSH, GT_UMOD))
    {
        range = ComputeRangeForBinOp(expr->AsOp() DEBUGARG(indent + 1));
    }
    // If phi, then compute the range for arguments, calling the result "dependent" when looping begins.
    else if (expr->OperGet() == GT_PHI)
    {
        range = MergePhi(expr, skipRecursivePhis DEBUGARG(indent + 1));
    }
    else if (varTypeIsSmallInt(expr->TypeGet()))
    {
        switch (expr->TypeGet())
        {
            case TYP_UBYTE:
                range = Range(Limit(Limit::keConstant, 0), Limit(Limit::keConstant, 255));
                break;
            case TYP_BYTE:
                range = Range(Limit(Limit::keConstant, -128), Limit(Limit::keConstant, 127));
                break;
            case TYP_USHORT:
                range = Range(Limit(Limit::keConstant, 0), Limit(Limit::keConstant, 65535));
                break;
            case TYP_SHORT:
                range = Range(Limit(Limit::keConstant, -32768), Limit(Limit::keConstant, 32767));
                break;
            default:
                range = Range(Limit(Limit::keUnknown));
                break;
        }

        JITDUMP("%s\n", range.ToString(m_pCompiler->getAllocatorDebugOnly()));
    }
    else if (expr->OperGet() == GT_COMMA)
    {
        range = GetRange(expr->gtEffectiveVal() DEBUGARG(indent + 1));
    }
    else
    {
        // The expression is not recognized, so the result is unknown.
        range = Range(Limit(Limit::keUnknown));
    }

    // TODO_Nathan: proper setting
    // GetRangeMap()->Set(expr, new (m_alloc) Range(range), RangeMap::Overwrite);
    return range;
}

// TODO_Nathan: Standard comment header
// Get the range, if it is already computed, use the cached range value, 
// else it is currently being computed. If so, then do stuff
Range RangeCheck::GetRange(GenTree* expr DEBUGARG(int indent))
{
    Range* pRange = nullptr; // TODO_Nathan: fix dumping
    Range  range(Limit::keUnknown);

    if (!GetRangeMap()->Lookup(expr, &range))
    {
#ifdef DEBUG
        if (m_pCompiler->verbose)
        {
            JITDUMP("Recursive dependency on ");
            m_pCompiler->gtDispTree(expr);
        }
#endif  
        assert(IsBeingWalked(expr));
        range = Range(Limit::keDependent);
        range.SetIsRecursive(true);
    }

    return range;
}

void RangeCheck::SetRange(GenTree* node, const Range& range)
{
    GetRangeMap()->Set(node, range, RangeCheck::RangeMap::Overwrite);
}

#ifdef DEBUG
// If this is a tree local definition add its location to the def map.
void RangeCheck::MapStmtDefs(const Location& loc)
{
    GenTreeLclVarCommon* tree = loc.tree;

    unsigned lclNum = tree->GetLclNum();
    unsigned ssaNum = tree->GetSsaNum();
    if (ssaNum == SsaConfig::RESERVED_SSA_NUM)
    {
        return;
    }

    // If useasg then get the correct ssaNum to add to the map.
    if (tree->gtFlags & GTF_VAR_USEASG)
    {
        unsigned ssaNum = m_pCompiler->GetSsaNumForLocalVarDef(tree);
        if (ssaNum != SsaConfig::RESERVED_SSA_NUM)
        {
            // To avoid ind(addr) use asgs
            if (loc.parent->OperIs(GT_ASG))
            {
                SetDef(HashCode(lclNum, ssaNum), new (m_alloc) Location(loc));
            }
        }
    }
    // If def get the location and store it against the variable's ssaNum.
    else if (tree->gtFlags & GTF_VAR_DEF)
    {
        if (loc.parent->OperGet() == GT_ASG)
        {
            SetDef(HashCode(lclNum, ssaNum), new (m_alloc) Location(loc));
        }
    }
}

struct MapMethodDefsData
{
    RangeCheck* rc;
    BasicBlock* block;
    Statement*  stmt;

    MapMethodDefsData(RangeCheck* rc, BasicBlock* block, Statement* stmt) : rc(rc), block(block), stmt(stmt)
    {
    }
};

Compiler::fgWalkResult MapMethodDefsVisitor(GenTree** ptr, Compiler::fgWalkData* data)
{
    GenTree*           tree = *ptr;
    MapMethodDefsData* rcd  = ((MapMethodDefsData*)data->pCallbackData);

    if (tree->IsLocal())
    {
        rcd->rc->MapStmtDefs(RangeCheck::Location(rcd->block, rcd->stmt, tree->AsLclVarCommon(), data->parent));
    }

    return Compiler::WALK_CONTINUE;
}

void RangeCheck::MapMethodDefs()
{
    // First, gather where all definitions occur in the program and store it in a map.
    for (BasicBlock* block = m_pCompiler->fgFirstBB; block != nullptr; block = block->bbNext)
    {
        for (Statement* stmt : block->Statements())
        {
            MapMethodDefsData data(this, block, stmt);
            m_pCompiler->fgWalkTreePre(stmt->GetRootNodePointer(), MapMethodDefsVisitor, &data, false, true);
        }
    }
    m_fMappedDefs = true;
}
#endif

// Entry point to range check optimizations.
void RangeCheck::OptimizeRangeChecks()
{
    if (m_pCompiler->fgSsaPassesCompleted == 0)
    {
        return;
    }
#ifdef DEBUG
    if (m_pCompiler->verbose)
    {
        JITDUMP("*************** In OptimizeRangeChecks()\n");
        JITDUMP("Blocks/trees before phase\n");
        m_pCompiler->fgDispBasicBlocks(true);
    }
#endif

    // Walk through trees looking for arrBndsChk node and check if it can be optimized.
    for (BasicBlock* block = m_pCompiler->fgFirstBB; block; block = block->bbNext)
    {
        for (Statement* stmt : block->Statements())
        {
            for (GenTree* tree = stmt->GetTreeList(); tree; tree = tree->gtNext)
            {
                if (IsOverBudget())
                {
                    return;
                }
                OptimizeRangeCheck(block, stmt, tree);
            }
        }
    }
}
