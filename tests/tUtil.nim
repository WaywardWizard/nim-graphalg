import unittest
import graphalg/util

suite "util: set bitvector scans":
  test "smallest/biggest on single element":
    var s: set[uint8]
    incl(s, 42'u8)
    check s.smallest() == 42
    check s.biggest() == 42

  test "smallest/biggest pick the extremes":
    var s: set[uint8]
    incl(s, 5'u8)
    incl(s, 100'u8)
    incl(s, 200'u8)
    check s.smallest() == 5
    check s.biggest() == 200

  test "boundary elements 0 and 255":
    var s: set[uint8]
    incl(s, 0'u8)
    incl(s, 255'u8)
    check s.smallest() == 0
    check s.biggest() == 255

  test "smallest updates after exclusion":
    var s: set[uint8]
    incl(s, 5'u8)
    incl(s, 100'u8)
    excl(s, 5'u8)
    check s.smallest() == 100

  test "empty set raises ValueError":
    var s: set[uint8]
    expect ValueError:
      discard s.smallest()
    expect ValueError:
      discard s.biggest()

  test "range subtype":
    type R = range[0'u8 .. 31'u8]
    var s: set[R]
    incl(s, 0'u8)
    incl(s, 31'u8)
    check s.smallest() == 0
    check s.biggest() == 31
