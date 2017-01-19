include "def.s.dfy"
module globals_s {

import opened ARM_def_s 

//-----------------------------------------------------------------------------
// Globals
//-----------------------------------------------------------------------------

function method K_SHA256s(): operand { OSymbol("g_k_sha256") }

function method KomGlobalDecls(): globaldecls
    ensures ValidGlobalDecls(KomGlobalDecls());
{
    map[K_SHA256s() := 256]
}

}
