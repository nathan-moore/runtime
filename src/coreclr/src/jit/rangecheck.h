// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

//
//
//  We take the following approach to range check analysis:
//
//  Consider the following loop:
//  for (int i = 0; i < a.len; ++i) {
//      a[i] = 0;
//  }
//
//  This would be represented as:
//              i_0 = 0; BB0
//               /        ______  a[i_1] = 0;     BB2
//              /        /        i_2 = i_1 + 1;
//             /        /          ^
//  i_1 = phi(i_0, i_2); BB1       |
//  i_1 < a.len -------------------+
//
//  BB0 -> BB1
//  BB1 -> (i_1 < a.len) ? BB2 : BB3
//  BB2 -> BB1
//  BB3 -> return
//
//  **Step 1. Walk the statements in the method checking if there is a bounds check.
//  If there is a bounds check, ask the range of the index variable.
//  In the above example i_1's range.
//
//  **Step 2. Follow the defs and the dependency chain:
//  i_1 is a local, so go to its definition which is i_1 = phi(i_0, i_2).
//
//  Since rhs is a phi, we ask the range for i_0 and i_2 in the hopes of merging
//  the resulting ranges for i_1.
//
//  The range of i_0 follows immediately when going to its definition.
//  Ask for the range of i_2, which leads to i_1 + 1.
//  Ask for the range of i_1 and figure we are looping. Call the range of i_1 as
//  "dependent" and quit looping further. The range of "1" is just <1, 1>.
//
//  Now we have exhausted all the variables for which the range can be determined.
//  The others are either "unknown" or "dependent."
//
//  We also merge assertions from its pred block's edges for a phi argument otherwise
//  from the block's assertionIn. This gives us an upper bound for i_1 as a.len.
//
//  **Step 3. Check if an overflow occurs in the dependency chain (loop.)
//  In the above case, we want to make sure there is no overflow in the definitions
//  involving i_1 and i_2. Merge assertions from the block's edges whenever possible.
//
//  **Step 4. Check if the dependency chain is monotonic.
//
//  **Step 5. If monotonic increasing is true, then perform a widening step, where we assume, the
//  SSA variables that are "dependent" get their lower bound values from the definitions in the
//  dependency loop and their initial values must be the definitions that are not in
//  the dependency loop, in this case i_0's value which is 0.
//

#pragma once
#include "compiler.h"

    static bool IntAddOverflows(int max1, int max2)
    {
        if (max1 > 0 && max2 > 0 && INT_MAX - max1 < max2)
        {
            return true;
        }
        if (max1 < 0 && max2 < 0 && max1 < INT_MIN - max2)
        {
            return true;
        }
        return false;
    }


struct Limit
{
    enum LimitType
    {
        keUndef, // The limit is yet to be computed.
        keBinOpArray,
        keConstant,
        keDependent, // The limit is dependent on some other value.
        keUnknown,   // The limit could not be determined. Lattice top
    };

    int       cns;
    ValueNum  vn;
    LimitType type;

    Limit() : type(keUndef)
    {
    }

    Limit(LimitType type) : type(type)
    {
    }

    Limit(LimitType type, int cns) : cns(cns), vn(ValueNumStore::NoVN), type(type)
    {
        assert(type == keConstant);
    }

    Limit(LimitType type, ValueNum vn, int cns) : cns(cns), vn(vn), type(type)
    {
        assert(type == keBinOpArray);
    }

    bool IsUndef() const
    {
        return type == keUndef;
    }
    bool IsDependent() const
    {
        return type == keDependent;
    }
    bool IsUnknown() const
    {
        return type == keUnknown;
    }
    bool IsConstant() const
    {
        return type == keConstant;
    }
    int GetConstant() const
    {
        return cns;
    }
    bool IsBinOpArray() const
    {
        return type == keBinOpArray;
    }
    bool AddConstant(int i)
    {
        switch (type)
        {
            case keDependent:
                return true;
            case keBinOpArray:
            case keConstant:
                if (IntAddOverflows(cns, i))
                {
                    return false;
                }
                cns += i;
                return true;
            case keUndef:
            case keUnknown:
                // For these values of 'type', conservatively return false
                break;
        }

        return false;
    }

    bool Equals(const Limit& l) const
    {
        switch (type)
        {
            case keUndef:
            case keUnknown:
            case keDependent:
                return l.type == type;

            case keBinOpArray:
                return l.type == type && l.vn == vn && l.cns == cns;

            case keConstant:
                return l.type == type && l.cns == cns;
        }
        return false;
    }
#ifdef DEBUG
    const char* ToString(CompAllocator alloc)
    {
        unsigned size = 64;
        char*    buf  = alloc.allocate<char>(size);
        switch (type)
        {
            case keUndef:
                return "Undef";

            case keUnknown:
                return "Unknown";

            case keDependent:
                return "Dependent";

            case keBinOpArray:
                sprintf_s(buf, size, FMT_VN " + %d", vn, cns);
                return buf;

            case keConstant:
                sprintf_s(buf, size, "%d", cns);
                return buf;
        }
        unreached();
    }
#endif
};

// Range struct contains upper and lower limit.
struct Range
{
    Limit uLimit;
    Limit lLimit;
    bool isRecursive;

    Range(const Limit& limit) : uLimit(limit), lLimit(limit), isRecursive(false)
    {
    }

    Range(const Limit& lLimit, const Limit& uLimit) : uLimit(uLimit), lLimit(lLimit), isRecursive(false)
    {
    }

    void SetIsRecursive(bool toSet)
    {
        isRecursive = toSet;
    }

    Limit& UpperLimit()
    {
        return uLimit;
    }

    Limit& LowerLimit()
    {
        return lLimit;
    }

    bool IsRecursive() const
    {
        return isRecursive;
    }

#ifdef DEBUG
    char* ToString(CompAllocator alloc)
    {
        size_t size = 64;
        char*  buf  = alloc.allocate<char>(size);
        sprintf_s(buf, size, "<%s, %s>", lLimit.ToString(alloc), uLimit.ToString(alloc));
        return buf;
    }
#endif
};

// Helpers for operations performed on ranges
struct RangeOps
{
    // Given a constant limit in "l1", add it to l2 and mutate "l2".
    static Limit AddConstantLimit(const Limit& l1, const Limit& l2)
    {
        assert(l1.IsConstant());
        Limit l = l2;
        if (l.AddConstant(l1.GetConstant()))
        {
            return l;
        }
        else
        {
            return Limit(Limit::keUnknown);
        }
    }

    static Limit Add(Limit& l1, Limit& l2, RangeCheck* rc)
    {
        if (rc->AddOverflows(l1, l2))
        {
            return Limit::keDependent;
        }

        if (l1.IsUnknown() || l2.IsUnknown())
        {
            return Limit(Limit::keUnknown);
        }
        else if (l1.IsDependent() || l1.IsDependent())
        {
            return Limit(Limit::keDependent);
        }
        else if (l1.IsConstant() || l2.IsConstant())
        {
            if (l1.IsConstant())
            {
                return AddConstantLimit(l1, l2);
            }
            else
            {
                return AddConstantLimit(l2, l1);
            }
        }
        else
        {
            return Limit(Limit::keUnknown);
        }
    }

    // Given two ranges "r1" and "r2", perform an add operation on the
    // ranges.
    static Range Add(Range& r1, Range& r2, RangeCheck* rc)
    {
        Limit& r1lo = r1.LowerLimit();
        Limit& r1hi = r1.UpperLimit();
        Limit& r2lo = r2.LowerLimit();
        Limit& r2hi = r2.UpperLimit();

        Range result = Limit(Limit::keUnknown);

        result.lLimit = Add(r1lo, r2lo, rc);
        result.uLimit = Add(r2lo, r2hi, rc);

        // Either Dependent or Unknown can overflow
        if (result.lLimit.IsDependent() || result.lLimit.IsUnknown())
        {
            result.uLimit = result.lLimit;
        }
        else if (result.uLimit.IsDependent() || result.uLimit.IsUnknown())
        {
            result.lLimit = result.uLimit;
        }

        return result;
    }

    // TODO: re-write this in terms of compares below
    // Given two ranges "r1" and "r2", do a Phi merge. If "monIncreasing" is true,
    // then ignore the dependent variables for the lower bound but not for the upper bound.
    static Range Merge(Range& r1, Range& r2)
    {
        Limit& r1lo = r1.LowerLimit();
        Limit& r1hi = r1.UpperLimit();
        Limit& r2lo = r2.LowerLimit();
        Limit& r2hi = r2.UpperLimit();

        // Take care of lo part.
        Range result = Limit(Limit::keUnknown);
        result.SetIsRecursive(r1.IsRecursive() || r2.IsRecursive());
        if (r1lo.IsUnknown() || r2lo.IsUnknown())
        {
            result.lLimit = Limit(Limit::keUnknown);
        }
        // Uninitialized, just copy.
        else if (r1lo.IsUndef())
        {
            result.lLimit = r2lo;
        }
        else if (r1lo.IsDependent() || r2lo.IsDependent())
        {
            // TODO_Nathan
            result.lLimit = Limit(Limit::keDependent);
        }

        // Take care of hi part.
        if (r1hi.IsUnknown() || r2hi.IsUnknown())
        {
            result.uLimit = Limit(Limit::keUnknown);
        }
        else if (r1hi.IsUndef())
        {
            result.uLimit = r2hi;
        }
        else if (r1hi.IsDependent() || r2hi.IsDependent())
        {
            result.uLimit = Limit(Limit::keDependent);
        }

        if (r1lo.IsConstant() && r2lo.IsConstant())
        {
            result.lLimit = Limit(Limit::keConstant, min(r1lo.GetConstant(), r2lo.GetConstant()));
        }
        if (r1hi.IsConstant() && r2hi.IsConstant())
        {
            result.uLimit = Limit(Limit::keConstant, max(r1hi.GetConstant(), r2hi.GetConstant()));
        }
        if (r2hi.Equals(r1hi))
        {
            result.uLimit = r2hi;
        }
        if (r2lo.Equals(r1lo))
        {
            result.lLimit = r1lo;
        }
        // Widen Upper Limit => Max(k, (a.len + n)) yields (a.len + n),
        // This is correct if k >= 0 and n >= k, since a.len always >= 0
        // (a.len + n) could overflow, but the result (a.len + n) also
        // preserves the overflow.
        if (r1hi.IsConstant() && r1hi.GetConstant() >= 0 && r2hi.IsBinOpArray() &&
            r2hi.GetConstant() >= r1hi.GetConstant())
        {
            result.uLimit = r2hi;
        }
        if (r2hi.IsConstant() && r2hi.GetConstant() >= 0 && r1hi.IsBinOpArray() &&
            r1hi.GetConstant() >= r2hi.GetConstant())
        {
            result.uLimit = r1hi;
        }
        if (r1hi.IsBinOpArray() && r2hi.IsBinOpArray() && r1hi.vn == r2hi.vn)
        {
            result.uLimit = r1hi;
            // Widen the upper bound if the other constant is greater.
            if (r2hi.GetConstant() > r1hi.GetConstant())
            {
                result.uLimit = r2hi;
            }
        }
        return result;
    }

    enum CompareResults {
        GreaterThen, // >
        LessThen, // <
        Equals, // ==
        CouldNotCompare
    };

    static CompareResults CompareLimit(const Limit& lhs, const Limit& rhs)
    {
        if (lhs.IsUnknown() || rhs.IsUnknown())
        {
            return CouldNotCompare;
        }

        if (lhs.IsDependent() || rhs.IsDependent())
        {
            if (lhs.IsDependent() && rhs.IsDependent())
            {
                return Equals;
            }
            else if (lhs.IsDependent())
            {
                return GreaterThen;
            }
            else
            {
                return LessThen;
            }
        }
        else if (rhs.Equals(lhs))
        {
            return Equals;
        }
        else if (rhs.IsConstant() && lhs.IsConstant())
        {
            int rhsConstant = rhs.GetConstant();
            int lhsConstant = lhs.GetConstant();
            assert(rhsConstant != lhsConstant);
            if (rhsConstant < lhsConstant)
            {
                return LessThen;
            }
            else
            {
                return GreaterThen;
            }
        }
        else if (rhs.IsBinOpArray() && lhs.IsBinOpArray())
        {
            // Note: these vns could be anything and could be valid, as we know that they are identical
            if (rhs.vn != lhs.vn)
            {
                return CouldNotCompare;
            }

            int rhsOffset = rhs.GetConstant();
            int lhsOffset = lhs.GetConstant();

            assert(rhsOffset != lhsOffset);
            if (rhsOffset < lhsOffset)
            {
                return LessThen;
            }
            else
            {
                return GreaterThen;
            }
        }
        else if (rhs.IsBinOpArray() && lhs.IsConstant())
        {
            // TODO: should really be checking the vn here, as it doesn't have to 
            // be a checked bound
            int rhsOffset = rhs.GetConstant();
            int lhsConstant = lhs.GetConstant();

            // Max(k, (a.len + n)) yields (a.len + n),
            // This is correct if k >= 0 and n >= k, since a.len always >= 0
            // (a.len + n) could overflow, but we account for that elsewhere
            // and it should be turned into the appropriete bound
            if (rhsOffset > lhsConstant)
            {
                return GreaterThen; // TODO_Nathan: potential CQ loss here, as we don't handle >=
            }
        }
        else if (rhs.IsConstant() && lhs.IsBinOpArray())
        {
            // TODO: should really be checking the vn here, as it doesn't have to 
            // be a checked bound
            int lhsOffset = lhs.GetConstant();
            int rhsConstant = rhs.GetConstant();

            if (rhsConstant < lhsOffset)
            {
                return LessThen; // TODO_Nathan: potential CQ loss here, as we don't handle >=
            }
        }

        return CouldNotCompare;
    }
};


class RangeCheck
{
public:
    // Constructor
    RangeCheck(Compiler* pCompiler);

    typedef JitHashTable<GenTree*, JitPtrKeyFuncs<GenTree>, bool>        OverflowMap;
    typedef JitHashTable<GenTree*, JitPtrKeyFuncs<GenTree>, Range>      RangeMap;
    typedef JitHashTable<GenTree*, JitPtrKeyFuncs<GenTree>, BasicBlock*> SearchPath;

#ifdef DEBUG
    // TODO-Cleanup: This code has been kept around just to ensure that the SSA data is still
    // valid when RangeCheck runs. It should be removed at some point (and perhaps replaced
    // by a proper SSA validity checker).

    // Location information is used to map where the defs occur in the method.
    struct Location
    {
        BasicBlock*          block;
        Statement*           stmt;
        GenTreeLclVarCommon* tree;
        GenTree*             parent;
        Location(BasicBlock* block, Statement* stmt, GenTreeLclVarCommon* tree, GenTree* parent)
            : block(block), stmt(stmt), tree(tree), parent(parent)
        {
        }

    private:
        Location();
    };

    typedef JitHashTable<INT64, JitLargePrimitiveKeyFuncs<INT64>, Location*> VarToLocMap;

    // Generate a hashcode unique for this ssa var.
    UINT64 HashCode(unsigned lclNum, unsigned ssaNum);

    // Add a location of the definition of ssa var to the location map.
    // Requires "hash" to be computed using HashCode.
    // Requires "location" to be the local definition.
    void SetDef(UINT64 hash, Location* loc);

    // Given a tree node that is a local, return the Location defining the local.
    Location* GetDef(GenTreeLclVarCommon* lcl);
    Location* GetDef(unsigned lclNum, unsigned ssaNum);

    // Given a statement, check if it is a def and add its locations in a map.
    void MapStmtDefs(const Location& loc);

    // Given the CFG, check if it has defs and add their locations in a map.
    void MapMethodDefs();
#endif

    int GetArrLength(ValueNum vn);

    // Check whether the computed range is within 0 and upper bounds. This function
    // assumes that the lower range is resolved and upper range is symbolic as in an
    // increasing loop.
    // TODO-CQ: This is not general enough.
    bool BetweenBounds(Range& range, GenTree* upper, int arrSize);

    // Entry point to optimize range checks in the block. Assumes value numbering
    // and assertion prop phases are completed.
    void OptimizeRangeChecks();

    // Given a "tree" node, check if it contains array bounds check node and
    // optimize to remove it, if possible. Requires "stmt" and "block" that
    // contain the tree.
    void OptimizeRangeCheck(BasicBlock* block, Statement* stmt, GenTree* tree);

    // Given the index expression try to find its range.
    // The range of a variable depends on its rhs which in turn depends on its constituent variables.
    // The "path" is the path taken in the search for the rhs' range and its constituents' range.
    // If "monIncreasing" is true, the calculations are made more liberally assuming initial values
    // at phi definitions for the lower bound.
    Range GetRange(GenTree* expr DEBUGARG(int indent));

    // Given the local variable, first find the definition of the local and find the range of the rhs.
    // Helper for GetRange.
    Range ComputeRangeForLocalDef(GenTreeLclVarCommon* lcl DEBUGARG(int indent));

    // Compute the range, rather than retrieve a cached value. Helper for GetRange.
    Range ComputeRange(GenTree* expr, bool widen DEBUGARG(int indent));

    // Compute the range for the op1 and op2 for the given binary operator.
    Range ComputeRangeForBinOp(GenTreeOp* binop DEBUGARG(int indent));

    // Merge assertions from AssertionProp's flags, for the corresponding "phiArg."
    // Requires "pRange" to contain range that is computed partially.
    void MergeAssertion(BasicBlock* block, GenTree* phiArg, Range* pRange DEBUGARG(int indent));

    // Inspect the "assertions" and extract assertions about the given "phiArg" and
    // refine the "pRange" value.
    void MergeEdgeAssertions(GenTreeLclVarCommon* lcl, ASSERT_VALARG_TP assertions, Range* pRange);

    Range MergePhi(GenTree* expr, bool widen DEBUGARG(int indent));

    // Inspect the assertions about the current ValueNum to refine pRange
    void MergeEdgeAssertions(ValueNum num, ASSERT_VALARG_TP assertions, Range* pRange);

    // The maximum possible value of the given "limit." If such a value could not be determined
    // return "false." For example: ARRLEN_MAX for array length.
    bool GetLimitMax(Limit& limit, int* pMax);

    // Does the addition of the two limits overflow?
    bool AddOverflows(Limit& limit1, Limit& limit2);

    // Does the binary operation between the operands overflow? Check recursively.
    bool DoesBinOpOverflow(GenTreeOp* binop);

    // Does the phi operands involve an assignment that could overflow?
    bool DoesPhiOverflow(GenTree* expr);

    // Find the def of the "expr" local and recurse on the arguments if any of them involve a
    // calculation that overflows.
    bool DoesVarDefOverflow(GenTreeLclVarCommon* lcl);

    bool ComputeDoesOverflow(GenTree* expr);

    // Does the current "expr" which is a use involve a definition, that overflows.
    bool DoesOverflow(GenTree* tree);

    // We allocate a budget to avoid walking long UD chains. When traversing each link in the UD
    // chain, we decrement the budget. When the budget hits 0, then no more range check optimization
    // will be applied for the currently compiled method.
    bool IsOverBudget();

    void SetRange(GenTree* node, const Range& range);

private:
    // https://msdn.microsoft.com/en-us/windows/apps/hh285054.aspx
    // CLR throws IDS_EE_ARRAY_DIMENSIONS_EXCEEDED if array length is > INT_MAX.
    // new byte[INT_MAX]; still throws OutOfMemoryException on my system with 32 GB RAM.
    // I believe practical limits are still smaller than this number.
    static const unsigned int ArrLen_Max = 0x7FFFFFFF;

    // Given a lclvar use, try to find the lclvar's defining assignment and its containing block.
    LclSsaVarDsc* GetSsaDefAsg(GenTreeLclVarCommon* lclUse);

    GenTreeBoundsChk* m_pCurBndsChk;

    // Get the cached overflow values.
    OverflowMap* GetOverflowMap();
    OverflowMap* m_pOverflowMap;

    // Get the cached range values.
    RangeMap* GetRangeMap();
    RangeMap* m_pRangeMap;

    SearchPath* m_pSearchPath;

#ifdef DEBUG
    bool         m_fMappedDefs;
    VarToLocMap* m_pDefTable;
#endif

    Compiler*     m_pCompiler;
    CompAllocator m_alloc;

    // The number of nodes for which range is computed throughout the current method.
    // When this limit is zero, we have exhausted all the budget to walk the ud-chain.
    int m_nVisitBudget;

    template <typename TVisitor>
    friend class DefinitionIterator;
};

template <typename TVisitor>
class DefinitionIterator : public GenTreeVisitor<TVisitor>
{
    typedef JitHashTable<GenTree*, JitPtrKeyFuncs<GenTree>, short> SearchPath;
protected:
    SearchPath* m_pPath;
    RangeCheck* m_pRangeCheck;
    short iterNum = 0;
    int depth = 0; // TODO: debug only
    bool error = false; // TODO_Better handling?
    bool widen = false;

    void PostOrderWalkNode(GenTree* node);

public:
    Compiler::fgWalkResult PreOrderVisit(GenTree** use, GenTree* user)
    {
        // TODO: skip subtrees
        depth++;
        return Compiler::WALK_CONTINUE;
    }

    Compiler::fgWalkResult PostOrderVisit(GenTree** use, GenTree* user)
    {
        GenTree* node = *use;
        if (node->IsLocal())
        {
            LclSsaVarDsc* ssaDef = m_pRangeCheck->GetSsaDefAsg(node->AsLclVarCommon());
            if (ssaDef == nullptr)
            {
                error = true;
                return Compiler::WALK_ABORT;
                // TODO: error
            }
            else
            {
                ((GenTreeVisitor<TVisitor>*)this)->WalkTree(&ssaDef->GetAssignment()->gtOp2, nullptr);
            }
        }
        else if (user->OperIs(GT_PHI))
        {
            for (GenTreePhi::Use& use : user->AsPhi()->Uses())
            {
                GenTree* useNode = use.GetNode();
                //TODO_Nathan: ??
                ((GenTreeVisitor<TVisitor>*)this)->WalkTree(&useNode, nullptr);
            }
        }

        Range range = m_pRangeCheck->ComputeRange(node, widen DEBUGARG(depth));
        WalkNodeRange(node, range DEBUGARG(depth));

        depth--;

        return Compiler::WALK_CONTINUE;
    }

    enum
    {
        DoPreOrder = true
    };

    void SetWiden(bool toWiden)
    {
        widen = toWiden;
    }

    void StartWalk(GenTree* node)
    {
        //TODO_Nathan: ??
        ((GenTreeVisitor<TVisitor>*)this)->WalkTree(&node, nullptr);
        iterNum++;
    }

    // TODO_Nathan: Better name
    void WalkNodeRange(GenTree* node, const Range& range DEBUGARG(int indent))
    {
        return;
    }

    DefinitionIterator(RangeCheck* rangeCheck)
        : GenTreeVisitor<TVisitor>(rangeCheck->m_pCompiler),
        m_pRangeCheck(rangeCheck)
    {
        m_pPath = new (m_pRangeCheck->m_alloc) SearchPath(m_pRangeCheck->m_alloc);
    }
};
