# dynarray
A High-utility implementation of a dynamic array in Java, similar to ArrayList

## benefits
+ Implements the Java List interface

+ Many extra functions, including range-based functions

+ Methods that take a Collection parameter have an identical overload that
  take an array parameter instead, including construction
  
+ Fine control over the starting capacity of the backing array and its growth increment

+ Partitioning

+ Option to set an internal comparator for an instance

+ When `sort()` is called or the DynArray is marked as sorted, either
  binary or combined binary and linear search are used in look-up
  dependent functions (e.g. calling `lastIndexOf(o)` on a sorted DynArray will result in it
  binary-searching for the value `o` and then linearly traversing the backing array
  until its last occurence is found.

+ A spliterator that splits elements *in order*
  
+ Thorough documentation

-- a bulk of this class was written circa 2020 --
