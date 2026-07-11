## Multiple elements of tsame value not accepted
import std/[lists, tables]
type IndexedList*[L: SomeLinkedList] = object
  list: L
  map: Table[L.T, typeof(default(L).head)]

proc `in`*(x: var IndexedList, val: IndexedList.L.T) =
  x.map.contains(val)

proc len*(x: IndexedList):int = x.map.len
iterator items*(x: IndexedList): IndexedList.L.T =
  for val in x.list: yield val
proc add*(x: var IndexedList, val: IndexedList.L.T) = # O(1)
  x.list.add val
  if val in x.map: raise ValueError.newException "Element data present already"
  x.map[val] = x.list.tail

proc prepend*(x: var IndexedList, val: IndexedList.L.T) = # O(1)
  x.list.prepend val
  if val in x.map: raise ValueError.newException "Element data present already"
  x.map[val] = x.list.head

proc del*(x: var IndexedList, val: IndexedList.L.T) = # O(1)
  x.list.remove x.map[val]
  x.map.del val

proc popFirst*(x: var IndexedList): IndexedList.L.T = # O(1)
  result = x.list.head.value
  x.list.remove x.list.head
  x.map.del result

proc popLast*(x: var IndexedList): IndexedList.L.T = # O(1)
  result = x.list.tail.value
  x.list.remove x.list.tail
  x.map.del result
