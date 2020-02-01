CALC_STMT
  | ``calc`` CALC_OP ``{`` CALC ... CALC EXP ``;`` ``}``
CALC
  | EXP ``;`` CALC_OP CALC_HINTS
CALC_OP
  | ``<`` | ``>`` | ``<=`` | ``>=`` | ``==``
  | ``&&`` | ``||`` | ``<==`` | ``==>`` | ``<==>``
CALC_HINTS
  | CALC_HINT ... CALC_HINT
CALC_HINT
  | ``{`` STMTS ``}``
