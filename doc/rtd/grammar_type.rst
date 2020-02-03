TYPE
  | **T**
  | TYPE ``(`` TYPE ``,`` ... ``,`` TYPE ``)``
  | ``tuple`` ``(`` TYPE ``,`` ... ``,`` TYPE ``)``
  | ``fun`` ``(`` TYPE ``,`` ... ``,`` TYPE ``)`` ``->`` TYPE
  | ``bool``
  | ``prop``
  | ``int``
  | ``int_range`` ``(`` _ ``,`` INT ``)``
  | ``int_range`` ``(`` INT ``,`` _ ``)``
  | ``int_range`` ``(`` INT ``,`` INT ``)``
  | ``dependent`` ``(`` **x** ``)``
  | ``(`` TYPE ``)``
