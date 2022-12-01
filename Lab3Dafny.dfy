// class CircularMemory
// This class implements a cicular buffer with with 2 int typed pointers

/*
Authors: Adam Williams, Jonathan Naumanen, Alexander Stenström
Group: 15
*/
class CircularMemory
{
  var cells : array<int>;
  var read_position : int;
  var write_position : int;
  var isFlipped : bool;

  constructor Init(cap : int)
    requires cap > 0
    ensures cap == cells.Length
    ensures read_position == 0
    ensures write_position == 0
    ensures isFlipped == false
  {
    cells := new int[cap];
    read_position, write_position := 0, 0;
    isFlipped := false;
  }

  predicate Valid() 
    reads this
  {
    // array can't be less than 1
    0 < cells.Length &&
    //write position needs to be inside index boundaries
    0 <= write_position < cells.Length && 
    //same with read position
    0 <= read_position < cells.Length && 
    //if the array is flipped, the write position needs to be greater than the read position
    (isFlipped ==> write_position <= read_position) && 
    //if the array is not flipped, the write position needs to be less than the read position
    (!isFlipped ==> write_position >= read_position)
  }

  predicate isEmpty()
    reads this
  {
    read_position == write_position && !isFlipped
  }

  predicate isFull()
    reads this
  {
    read_position == write_position && isFlipped
  }

  method Read() returns (isSuccess : bool, content : int)
    modifies this
    requires Valid()
    ensures Valid()
    ensures  isSuccess ==> content == old(cells[(read_position)])
    ensures !isSuccess ==> content == 0
    ensures !isSuccess ==> read_position == old(read_position)
    ensures cells.Length == old(cells.Length)
  {
    if(isFlipped) //om flipped write kan inte gå förbi read om !flipped read kan inte gå förbi write
    {
      isSuccess := true;
      content := cells[read_position];
      read_position := read_position + 1;
      if(read_position == cells.Length){
        isFlipped := false;
        read_position := 0;
      }
    }
    else // not flipped
    {
      if(read_position == write_position){
        isSuccess := false;
        content := 0;
      } 
      else {
      isSuccess := true;
      content := cells[read_position];
      read_position := read_position + 1;
      }
    }
  }

  method Write(input : int) returns (isSuccess : bool)
    modifies cells, `write_position, `isFlipped
    requires Valid()
    ensures Valid()
    ensures  isSuccess ==> cells[old(write_position)] == input
    ensures !isSuccess ==> cells[(write_position)] == old(cells[(write_position)])
    ensures !isSuccess ==> write_position == old(write_position)
    ensures cells.Length == old(cells.Length)
  {
    if(!isFlipped)
    {
      isSuccess := true;
      cells[write_position] := input; 
      write_position := (write_position + 1);
      if(write_position == cells.Length){
        write_position := 0;
        isFlipped := true;
      }
    }
    else // flipped
    {
      if(write_position == read_position){
        isSuccess := false;
      } 
      else {
      isSuccess := true;
      cells[write_position] := input; 
      write_position := (write_position + 1);
      }
    }

  }
}
