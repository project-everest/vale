EXP
  | **x**
  | **F**
  | ``true`` | ``false``
  | INT
  | 0.1 | 0.2 | ... | 3.14159 | ...
  | ``bv16`` ``(`` 0xbeef ``)`` | ``bv64`` ``(`` 7 ``)`` | ...
  | ``"`` STRING ``"``
  | ``(`` ``-`` EXP ``)``
  | ``this``
  | ``@`` **x**

  | EXP ``(`` EXP ``,`` ... ``,`` EXP ``)``
  | **F** ``#[`` TYPE ``,`` ... ``,`` TYPE ``]``
  |   ``(`` EXP ``,`` ... ``,`` EXP ``)``
  | ``#`` TYPE ``(`` EXP ``)``

  | EXP ``[`` EXP ``]``
  | EXP ``[`` EXP ``:=`` EXP ``]``
  | EXP ``?[`` EXP ``]``
  | EXP ``.`` **D**
  | EXP ``.`` ``(`` **D** ``:=`` EXP ``)``

  | ``old`` ``(`` EXP ``)``
  | ``old`` ``[`` EXP ``]`` ``(`` EXP ``)``

  | seq ``(`` EXP ``,`` ... ``,`` EXP ``)``
  | set ``(`` EXP ``,`` ... ``,`` EXP ``)``
  | list ``(`` EXP ``,`` ... ``,`` EXP ``)``
  | ``tuple`` ``(`` EXP ``,`` ... ``,`` EXP ``)``

  | ``!`` EXP

  | EXP ``*`` EXP | EXP ``/`` EXP | EXP ``%`` EXP
  | EXP ``+`` EXP | EXP ``-`` EXP
  | EXP ``<`` EXP | EXP ``>`` EXP
  | EXP ``<=`` EXP | EXP ``>=`` EXP
  | EXP ``is`` **C**
  | EXP ``==`` EXP | EXP ``!=`` EXP
  | EXP ``&&`` EXP
  | EXP ``||`` EXP
  | EXP ``<==`` EXP | EXP ``==>`` EXP
  | EXP ``<==>`` EXP

  | ``if`` EXP ``then`` EXP ``else`` EXP
  | ``let`` FORMAL ``:=`` EXP ``in`` EXP

  | ``forall`` ``(`` FORMALS ``)`` TRIGGERS EXP
  | ``exists`` ``(`` FORMALS ``)`` TRIGGERS EXP
  | ``fun``    ``(`` FORMALS ``)`` TRIGGERS EXP

  | ``(`` EXP ``)``
