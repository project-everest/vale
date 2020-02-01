SPECS
  | SPEC ... SPEC
SPEC
  | ``reads`` **x** ``;`` ... **x** ``;``
  | ``modifies`` **x** ``;`` ... **x** ``;``
  | ``lets`` LETBIND ``;`` ... LETBIND ``;``
  | ``requires`` LEXP ``;`` ... LEXP ``;``
  | ``ensures`` LEXP ``;`` ... LEXP ``;``
  | ``requires`` ``/`` ``ensures`` LEXP ``;`` ... LEXP ``;``
LETBIND
  | FORMAL ``:=`` EXP
  | **x1** ``@=`` **x2**
LEXP
  | EXP
  | ``let`` FORMAL ``:=`` EXP
