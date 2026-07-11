import macros, std/bitops
proc count*(x: iterator): int =
  for _ in x:
    result += 1

type CountFrom = enum
  cfMSB
  cfLSB

macro reverse(stmts: typed): untyped =
  stmts.expectKind nnkStmtList
  result = newStmtList()
  for ix in 1 .. stmts.len():
    result.add stmts[^ix]

proc zeroCount[T](x: set[T], cfrom = cfLSB): T =
  ## Return the smallest (ordinally) T in x
  ##
  ## Words are least to most significant in memory. Binary printed or represented
  ## reads MSB to LSB, or LSB on the left to MSB on the right.
  ##
  ## The smallest element will be the one with a value 1 in the least significant
  ## position. The greatest will have a 1 in the most significant. Leading zeros
  ## index the biggest item. zeroes the smallest.
  ##
  ## A byte (B) is 8 bits (b).
  ## A word is 2B/16b, dword is 4B/32b, qword is 8B/64b, oword 16B/128b
  ## These correspond to uint8, uint16, uint32, uint64, uint128
  ##
  ## Why? set[T] is a bitvector, and quick to work with. Speed.

  const sz = sizeof(x)
  let xptr = cast[uint](addr x) # pointer for arithmetic
  when sz div 8 > 0: # LTR order, initial bytes
    let qwords = cast[ptr array[sz div 8, uint64]](xptr)
  when (sz mod 8) div 4 > 0: # LTR, after qwords
    let dword = cast[ptr uint32](xptr + (8 * (sz div 8)))
  when (sz mod 4) div 2 > 0: # LTR, after dword
    let word = cast[ptr uint16](xptr + 8 * (sz div 8) + 4 * ((sz mod 8) div 4))
  when (sz mod 2) > 0: # LTR, final byte
    let bbyte = cast[ptr uint8](xptr + sz - 1)

  var zeroes: int
  var found = false
  var tmp: int

  template scan(apply: untyped, leftwards: bool = false) =
    ## Apply proc to chunked memory left to right/LSB->MSB (right to left MSB->LSB)
    template ltr() =
      when declared(qwords):
        if not found:
          for ix in 1 .. (len qwords[]):
            let qw =
              if leftwards:
                qwords[][^ix]
              else:
                qwords[][ix - 1]
            if qw == 0:
              zeroes += 64
            else:
              found = true
              zeroes += apply(qw)
              break
      when declared(dword):
        if not found:
          if dword[] == 0:
            zeroes += 32
          else:
            found = true
            zeroes += apply(dword[])
      when declared(word):
        if not found:
          if word[] == 0:
            zeroes += 16
          else:
            found = true
            zeroes += apply(word[])
      when declared(bbyte):
        if not found:
          if bbyte[] == 0:
            zeroes += 8
          else:
            found = true
            zeroes += apply(bbyte[])

    if leftwards:
      reverse:
        ltr
    else:
      ltr

  if cFrom == cfMSB: # count zeros from LSB to first flipped
    # this is leading according to writing convention of MSB-LSB
    scan(countLeadingZeroBits, true)
  else:
    scan(countTrailingZeroBits)

  cast[T](zeroes)

proc smallest*[T](x: set[T]): T =
  result = x.zeroCount(cfLSB)
  if result == 0 and x.card == 0:
    raise ValueError.newException("Empty set has no smallest element")

proc biggest*[T](x: set[T]): T =
  let z = x.zeroCount(cfMSB)
  if z == 0 and x.card == 0: # empty set vs biggest element present
    raise ValueError.newException("Empty set has no biggest element")
  sizeof(x) * 8 - 1 - z
