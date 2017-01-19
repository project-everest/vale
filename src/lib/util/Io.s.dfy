extern "Io_s" module Io_s {

class HostEnvironment
{
    ghost var constants:HostConstants;

    constructor{:axiom} () //requires false;

    predicate Valid()
        reads this;
    {
           constants != null
        && allocated(constants)
    }
}

//////////////////////////////////////////////////////////////////////////////
// Per-host constants
//////////////////////////////////////////////////////////////////////////////

extern "HostConstants" class HostConstants
{
    constructor{:axiom} () requires false;

    // result of C# System.Environment.GetCommandLineArgs(); argument 0 is name of executable
    function {:axiom} CommandLineArgs():seq<seq<char>> reads this; 

    extern "NumCommandLineArgs" static method NumCommandLineArgs(ghost env:HostEnvironment) returns(n:int)
        requires env != null && allocated(env) && env.Valid();
        ensures  n == |env.constants.CommandLineArgs()|;
        ensures  0 <= n < 0x1_0000_0000;

    extern "GetCommandLineArg" static  method GetCommandLineArg(i:nat, ghost env:HostEnvironment) returns(arg:array<char>)
        requires env != null && allocated(env) && env.Valid();
        requires 0 <= i < |env.constants.CommandLineArgs()|;
        ensures  arg != null;
        ensures  fresh(arg);
        ensures  arg[..] == env.constants.CommandLineArgs()[i];
}

}
