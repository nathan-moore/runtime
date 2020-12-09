using System;
// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System;

class Program
{
    public static int Main(string[] args)
    {
        int[] arr = new int[10] {5, 5, 5, 5, 5, 5, 5, 5, 5, 5};
        int sum = LongSum(arr);
        sum += NintSum(arr);
        try { LongConstantBoundedLoop(arr); return 0; } catch (IndexOutOfRange) {}
        try { LongConstantIndex(arr); return 0; } catch (IndexOutOfRange) {}

        return sum;
    }

    public static int LongSum(int[] arr)
    {
        int sum = 0;
        for (long i = 0; i < arr.Length; i++)
        {
            sum += arr[i];
        }
        return sum;
    }

    public static int NintSum(int[] arr)
    {
        int sum = 0;
        for (nint i = 0; i < arr.Length; i++)
        {
            sum += arr[i];
        }
        return sum;
    }

    public static int NintSum(int[] arr)
    {
        int sum = 0;
        for (long i = 0; i < arr.Length - 1; i++)
        {
            sum += arr[i + 1L];
        }
        return sum;
    }

    public static int LongConstantBoundedLoop(int[] arr)
    {
        if (arr.Length >= 10)
        {
            int sum = 0;
            for (long i = (1 << 32); i < ((1 << 32) + 5); i++)
            {
                sum += arr[i];
            }
            return sum;
        }
        else
        {
            return -1;
        }
    }

    public static int LongConstantIndex(int[] arr)
    {
        if (arr.Length >= 10)
        {
            return arr[((1L << 32)];
        }
    }
}