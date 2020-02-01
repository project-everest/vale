STMTS
  | STMT ... STMT
STMT
  | ``assume`` EXP ``;``
  | ``assert`` EXP ``;``
  | ``assert`` *[* EXP ``implies`` *]* EXP ``by`` ``{`` STMTS ``}``
  | ``forall`` ``(`` FORMALS ``)`` TRIGGERS
  |   *[* EXP ``implies`` *]* EXP ``by`` ``{`` STMTS ``}``

  | ``let`` **x** *[* ``:`` TYPE *]* ``:=`` EXP ``;``
  | ``let`` **x1** ``@=`` **x2** ``;``
  | ``ghost`` ``var`` **x** *[* ``:`` TYPE *]* *[* ``:=`` EXP *]* ``;``
  | ``let`` ``exists`` ``(`` FORMALS ``)`` TRIGGERS
  |   EXP ``;``

  | ``reveal`` **F** ``;``
  | ``reveal`` **F** ``(`` EXP ``,`` ... ``,`` EXP ``)`` ``;``

  | **p** ``(`` EXP ``,`` ... ``,`` EXP ``)`` ``;``
  | DESTINATIONS ``:=``
  |   **p** ``(`` EXP ``,`` ... ``,`` EXP ``)`` ``;``
  | **x** ``:=`` EXP ``;``
  | ``this`` ``:=`` EXP ``;``

  | ``while`` ``(`` EXP ``)``
  |   INVARIANTS DECREASE
  |   ``{`` STMTS ``}``

  | *[* ``ghost`` *]* *[* ``inline`` *]*
  |   ``if`` ``(`` EXP ``)`` ``{`` STMTS ``}``
  |   *[* ``else`` ``if`` ``(`` EXP ``)`` ``{`` STMTS ``}``
  |   ... ``else`` ``if`` ``(`` EXP ``)`` ``{`` STMTS ``}`` *]*
  |   *[* ``else`` ``{`` STMTS ``}`` *]*

  | CALC_STMT
