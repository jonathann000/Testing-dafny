// class CircularMemory
// This class implements a cicular buffer with with 2 int typed pointers
class CircularMemory
{
  var cells : array<int>;
  var read_position : int;
  var write_position : int;
  var isFlipped : bool;


  constructor Init(cap : int) 
    requires cap > 0;
    ensures cells.Length == cap;
    ensures read_position == 0;
    ensures write_position == 0;
    ensures isFlipped == false;
  {
    cells := new int[cap];
    read_position := 0;
    write_position := 0;
    isFlipped := false;
    // missing some pre-condition checks
  }
  predicate Valid()
    reads this
  {
    cells.Length > 0 &&
    read_position >= 0 && read_position < cells.Length &&
    write_position >= 0 && write_position < cells.Length &&
    (isFlipped ==> read_position <= write_position) &&
    (!isFlipped ==> read_position > write_position)
  }

    
  predicate isEmpty()
    reads this
    requires Valid();
    ensures isEmpty() <==> (read_position == write_position && !isFlipped);
  {
    read_position == write_position && !isFlipped
  }

  predicate isFull()
    reads this
    requires Valid();
    ensures isFull() <==> (read_position == write_position && isFlipped);
  {
    read_position == write_position && isFlipped
  }


  method Read() returns (isSuccess : bool, content : int)
    modifies this
    requires Valid();
    requires !isEmpty();
    ensures Valid();
    ensures isSuccess ==> content == old(cells[read_position]);
    ensures !isSuccess ==> content == 0;
    ensures cells.Length == old(cells.Length);
  {
    if(isFlipped) // returns current and advances read position 
    {
      isSuccess := false;
      content := 0;   
    }
    else {
      isSuccess := true;
      content := cells[read_position];
      read_position := read_position + 1;
      if(read_position == cells.Length) {
        isFlipped := true;
        read_position := 0;
      }
    }
  }

  method Write(input : int) returns (isSuccess : bool)
    modifies this
    modifies cells[write_position]
    requires Valid();
    requires !isFull();
    ensures Valid();
    ensures isSuccess ==> input == old(cells[write_position]);
    ensures !isSuccess ==> cells[write_position] == old(cells[write_position]);
    ensures cells.Length == old(cells.Length);
  {
    if(isFlipped) // writes input and advances write position
    {
      isSuccess := true;
      cells[write_position] := input;
      write_position := write_position + 1;
      if(write_position == cells.Length) {
        isFlipped := false;
        write_position := 0;
      }
    }
    else {
      isSuccess := false;
    }
  }

}
