open Prims
let (uint64_to_uint128 : FStar_UInt64.t -> FStar_UInt128.t) =
  fun a  -> FStar_UInt128.uint64_to_uint128 a 
let (uint128_to_uint64 : FStar_UInt128.t -> FStar_UInt64.t) =
  fun a  -> FStar_UInt128.uint128_to_uint64 a 