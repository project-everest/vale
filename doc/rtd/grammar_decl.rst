DECL
  | ``type`` **T** *[* ``(`` TFORMALS ``)`` *]* ``:``
      KIND ``extern``
      ``;``
  | ``type`` **T** *[* ``(`` TFORMALS ``)`` *]* ``:``
      KIND ``:=`` TYPE ``;``
  | ``operand_type`` **O** *[* ``(`` PFORMALS ``)`` *]*
      ``:`` TYPE
  |   *[* ``@`` TYPE *]* *[* ``:=`` OTYPS *]* ``;``

  | ``var`` **x** ``:`` TYPE ``;``
  | ``const`` **x** ``:`` TYPE ``extern`` ``;``
  | ``function`` **F** *[* ``#[`` TFORMALS ``]`` *]*
    ``(`` FORMALS ``)``
  |   ``:`` FRET SPECS ``extern`` ``;``
  | ``function`` **F** ``(`` FORMALS ``)`` ``:`` TYPE
    ``:=`` **F** ``;``

  | *[* ``ghost`` *]* ``procedure`` **P**
  |     *[* ``#[`` TFORMALS ``]`` *]* ``(`` PFORMALS ``)``
  |     *[* ``returns`` ``(`` PRETS ``)`` *]* SPECS ``{`` STMTS ``}``
  | *[* ``ghost`` *]* ``procedure`` **P**
  |     *[* ``#[`` TFORMALS ``]`` *]* ``(`` PFORMALS ``)``
  |     *[* ``returns`` ``(`` PRETS ``)`` *]* SPECS ``extern`` ``;``

  | VERBATIM_DECL_BLOCK

