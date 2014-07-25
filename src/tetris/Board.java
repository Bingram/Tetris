/*
 * An implementation of the classic game "Tetris".
 * 
 * @author "Daniel M. Zimmerman (dmz@acm.org)"
 * @module "TCSS 305"
 * @creation_date "July 2008"
 * @last_updated_date "October 2012"
 * @keywords "Tetris", "game"
 */

package tetris;

import java.awt.Color;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Observable;

import tetris.piecegen.PieceGenerator;
import tetris.piecegen.RandomGenerator;
import tetris.piecegen.SequenceGenerator;
import tetris.pieces.AbstractPiece;
import tetris.pieces.Piece;
import tetris.util.Point;


/**
 * A list of rows comprising the gameplay area.
 *
 * @author Daniel M. Zimmerman (dmz@acm.org)
 * @version October 2012
 */
public class Board extends Observable 
{
  /**
   * The number of rows that exist above the visible board area.
   */
  public static final int ROWS_ABOVE_BOARD = Piece.NUMBER_OF_BLOCKS;

  /**
   * The character used in the String representation to represent a
   * side border.
   */
  public static final char SIDE_BORDER_CHAR = '|';

  /**
   * The character used in the String representation to represent the
   * bottom border.
   */
  public static final char BOTTOM_BORDER_CHAR = '-';

  /**
   * The character used in the String representation to represent an
   * empty block.
   */
  public static final char EMPTY_BLOCK_CHAR = ' ';

  /**
   * The character used in the String representation to represent a
   * frozen block.
   */
  public static final char FROZEN_BLOCK_CHAR = 'X';

  /**
   * The character used in the String representation to represent a
   * block of the current piece.
   */
  public static final char CURRENT_PIECE_BLOCK_CHAR = '+';

  // Instance Fields

  /**
   * The height.
   */
  private final int my_height;

  /**
   * The width.
   */
  private final int my_width;

  /**
   * The list of rows.
   */
  private final /*@ non_null @*/ List<Color[]> my_row_list;

  /**
   * The piece generator used by this board.
   */
  private final /*@ non_null @*/ PieceGenerator my_piece_generator;

  /**
   * The current piece.
   */
  private /*@ non_null @*/ Piece my_current_piece;

  /**
   * The next piece.
   */
  private /*@ non_null @*/ Piece my_next_piece;

  /**
   * The number of lines removed as a result of the last move or drop.
   */
  private int my_last_lines_removed;

  /**
   * The number of blocks placed as a result of the last move or drop.
   */
  private int my_last_blocks_placed;

  /**
   * A flag indicating whether or not the board changed as a result of
   * the last action.
   */
  private boolean my_changed_flag;

  /**
   * A flag indicating whether or not the board is full.
   */
  private boolean my_full_flag;

  // Constructor

  //@ requires 0 < the_height;
  //@ requires 0 < the_width;
  //@ ensures height == the_height;
  //@ ensures width == the_width;
  //@ ensures last_lines_removed == 0;
  //@ ensures last_blocks_placed == 0;
  //@ ensures changed;
  //@ ensures !full;
  /**
   * Constructs a new board with the specified dimensions and the
   * specified random seed for the piece generator.
   *
   * @param the_height The height.
   * @param the_width The width.
   * @param the_seed The random seed.
   */
  public Board(final int the_height, final int the_width, final long the_seed) 
  {
    super();
    my_height = the_height;
    my_width = the_width;
    my_piece_generator =
      new RandomGenerator(the_seed, new Point(the_width / 2, the_height));
    my_row_list = new LinkedList<Color[]>();
    initialize();
  }

  //@ requires 0 < the_height;
  //@ requires 0 < the_width;
  //@ requires 0 < the_sequence.size();
  /*@ requires
      (\forall int i; 0 <= i && i < the_sequence.size();
       the_sequence.get(i) != null); @*/
  //@ ensures height == the_height;
  //@ ensures width == the_width;
  //@ ensures last_lines_removed == 0;
  //@ ensures last_blocks_placed == 0;
  //@ ensures changed;
  //@ ensures !full;
  /**
   * Constructs a new board with the specified dimensions and the
   * specified sequence of pieces to use.
   *
   * @param the_height The height.
   * @param the_width The width.
   * @param the_sequence The sequence.
   */
  public Board(final int the_height, final int the_width,
               final /*@ non_null @*/ List<AbstractPiece> the_sequence) 
  {
    super();
    my_height = the_height;
    my_width = the_width;
    my_piece_generator = new SequenceGenerator(the_sequence);
    my_row_list = new LinkedList<Color[]>();
    initialize();
  }

  /**
   * @return What is your height?
   */
  public /*@ pure @*/ int height() 
  {
    return my_height;
  }

  /**
   * @return What is your width?
   */
  public /*@ pure @*/ int width() 
  {
    return my_width;
  }

  //@ requires 0 <= the_y && the_y < height() + ROWS_ABOVE_BOARD;
  /**
   * @param the_y The y-coordinate of the desired row.
   * @return What is the row of frozen pieces at position the_y?
   * (note that this returns a clone)
   */
  public /*@ pure non_null @*/ Color[] rowAt(final int the_y) 
  {
    Color[] result = (Color[]) my_row_list.get(the_y);
    result = (Color[]) result.clone();
    return result;
  }

  //@ requires 0 <= the_y && the_y < height() + ROWS_ABOVE_BOARD;
  /**
   * @param the_y The row position.
   * @return Is the row at position the_y, _not_ including the current piece,
   * empty?
   */
  public /*@ pure @*/ boolean isRowEmpty(final int the_y) 
  {
    boolean result = true;
    for (int i = 0; i < Piece.NUMBER_OF_BLOCKS; i++) 
    {
      result = result && !(currentPiece().absolutePosition(i).y() == the_y);
    }
    for (int x = 0; x < my_width; x++) 
    {
      result = result && rowAt(the_y)[x] == null;
    }
    return result;
  }

  //@ requires 0 <= the_y && the_y < height() + ROWS_ABOVE_BOARD;
  /**
   * @param the_y The row position.
   * @return Is the row at position the_y, including the current piece,
   * full?
   */
  public /*@ pure @*/ boolean isRowFull(final int the_y) 
  {
    final Color[] row = rowAt(the_y);
    for (int i = 0; i < Piece.NUMBER_OF_BLOCKS; i++) 
    {
      final Point block_pos = currentPiece().absolutePosition(i);
      if (block_pos.y() == the_y) 
      {
        row[block_pos.x()] = currentPiece().color();
      }
    }
    boolean result = true;
    for (int x = 0; x < my_width; x++) 
    {
      result = result && row[x] != null;
    }
    return result;
  }

  //@ requires 0 <= the_y && the_y < height() + ROWS_ABOVE_BOARD;
  /**
   * @param the_y The row position.
   * @return Is the row at position the_y, not including the current piece,
   * full?
   */
  private /*@ pure @*/ boolean isFrozenRowFull(final int the_y) 
  {
    final Color[] row = rowAt(the_y);
    boolean result = true;
    for (int x = 0; x < my_width; x++) 
    {
      result = result && row[x] != null;
    }
    return result;
  }
  
  //@ requires 0 <= the_y && the_y < height() + ROWS_ABOVE_BOARD;
  /**
   * @param the_y The row position.
   * @return Is the row at position the_y, including the projection of
   * the current piece, full?
   */
  public /*@ pure @*/ boolean isRowFullUnderProjection(final int the_y) 
  {
    boolean result = true;
    final Piece projection = projection();
    for (int i = 0; i < my_width; i++) 
    {
      if (rowAt(the_y)[i] == null) 
      {
        boolean occupied = false;
        for (int j = 0; j < Piece.NUMBER_OF_BLOCKS; j++) 
        {
          final Point block_pos = projection.absolutePosition(i);
          if (block_pos.x() == i && block_pos.y() == the_y) 
          {
            occupied = true;
          }
        }
        result = result && occupied;
      }
    }
    return result;
  }

  /**
   * @param the_point The position.
   * @return What color is the block at position (the_x, the_y) (including
   * blocks in the current piece)?
   */
  public /*@ pure nullable @*/ Color color(final Point the_point) 
  {
    Color result = rowAt(the_point.y())[the_point.x()];
    if (result == null) 
    {
      // see if the current piece has a block there
      for (int i = 0; i < Piece.NUMBER_OF_BLOCKS && (result == null); i++) 
      {
        final Point p = currentPiece().absolutePosition(i);
        if (p.equals(the_point)) 
        {
          result = currentPiece().color();
        }
      }
    }
    return result;
  }

  /**
   * @param the_piece The piece.
   * @return Does the_piece collide with the already-frozen pieces or
   * the boundaries of the board?
   */
  public /*@ pure @*/ boolean collides(final /*@ non_null @*/ Piece the_piece) 
  {
    boolean result = false;
    for (int i = 0; !result && i < Piece.NUMBER_OF_BLOCKS; i++) 
    {
      final Point block_pos = the_piece.absolutePosition(i);
      result = result || !isWithinBoard(block_pos);
      result = result || rowAt(block_pos.y())[block_pos.x()] != null;
    }
    return result;
  }

  /**
   * @return How many lines were removed as a result of the last action?
   */
  public /*@ pure @*/ int lastLinesRemoved() 
  {
    return my_last_lines_removed;
  }

  /**
   * @return How many blocks were placed as a result of the last action?
   */
  public /*@ pure @*/ int lastBlocksPlaced() 
  {
    return my_last_blocks_placed;
  }

  /**
   * @return Did the state of the board change as a result of the last action?
   */
  public /*@ pure @*/ boolean changed() 
  {
    return my_changed_flag;
  }

  /**
   * @return What is the current piece? (returns a clone since pieces are mutable)
   */
  public /*@ pure non_null @*/ Piece currentPiece() 
  {
    Piece result = null;
    try
    {
      result = ((AbstractPiece) my_current_piece).clone();
    }
    catch (final CloneNotSupportedException e)
    {
      // this should never happen
      assert false;
    }
    return result;
  }

  /**
   * @return What is the projection of the current piece?
   */
  public /*@ pure non_null @*/ Piece projection() 
  {
    Piece projection = null;
    try
    {
      projection = ((AbstractPiece) my_current_piece).clone();
      final Piece next_move = ((AbstractPiece) my_current_piece).clone();
      next_move.moveDown();
      while (!collides(next_move)) 
      {
        projection.moveDown();
        next_move.moveDown();
      }
    }
    catch (final CloneNotSupportedException e)
    {
      // this should never happen
      assert false;
    }
    return projection;
  }

  /**
   * @return What is the next piece? (returns a clone since pieces are mutable)
   */
  public /*@ pure non_null @*/ Piece nextPiece() 
  {
    Piece result = null;
    try
    {
      result = ((AbstractPiece) my_next_piece).clone();
    }
    catch (final CloneNotSupportedException e)
    {
      // this should never happen
      assert false;
    }
    return result;
  }

  /**
   * @return Is the board full?
   */
  //@ ensures \result == full;
  public /*@ pure @*/ boolean isFull() 
  {
    return my_full_flag;
  }

  // Commands

  /**
   * Move the current piece left, if possible!
   */
  public void moveLeft() 
  {
    try
    {
      my_last_lines_removed = 0;
      my_last_blocks_placed = 0;
      my_changed_flag = false;
      final Piece moved = ((AbstractPiece) currentPiece()).clone();
      moved.moveLeft();
      if (!collides(moved)) 
      {
        my_current_piece = moved;
        my_changed_flag = true;
        setChanged();
      }
      notifyObservers();
    }
    catch (final CloneNotSupportedException e)
    {
      // this should never happen
      assert false;
    }
  }
  
  /**
   * Move the current piece right, if possible!
   */
  public void moveRight() 
  {
    try
    {
      my_last_lines_removed = 0;
      my_last_blocks_placed = 0;
      my_changed_flag = false;
      final Piece moved = ((AbstractPiece) currentPiece()).clone();
      moved.moveRight();
      if (!collides(moved)) 
      {
        my_current_piece = moved;
        my_changed_flag = true;
        setChanged();
      }
      notifyObservers();
    }
    catch (final CloneNotSupportedException e)
    {
      // this should never happen
      assert false;
    }
  }

  /**
   * Move the current piece down, if possible!
   */
  public void moveDown() 
  {
    Piece moved = null;
    try
    {
      moved = ((AbstractPiece) currentPiece()).clone();
      moved.moveDown();
    }
    catch (final CloneNotSupportedException e)
    {
      // this should never happen
      assert false;
    }
    my_last_lines_removed = 0;
    if (collides(moved)) 
    {
      // freeze the current piece
      for (int i = 0; i < Piece.NUMBER_OF_BLOCKS; i++) 
      {
        final Point block_pos = currentPiece().absolutePosition(i);
        ((Color[]) my_row_list.get(block_pos.y()))[block_pos.x()] =
          currentPiece().color();
      }

      // clear all full rows
      clearFullRows();

      // check for end of game
      for (int y = height(); !my_full_flag && y < my_row_list.size(); y++) 
      {
        my_full_flag = isRowEmpty(y);
        my_full_flag ^= true; // bitwise inversion
      }

      // add empty rows at the top
      for (int i = 0; i < my_last_lines_removed; i++) 
      {
        my_row_list.add(new Color[my_width]);
      }

      // replace the current piece with the next piece, and adjust
      // my_last_blocks_placed
      my_current_piece = my_next_piece;
      my_next_piece = my_piece_generator.next();
      my_last_blocks_placed = Piece.NUMBER_OF_BLOCKS;
    } 
    else 
    {
      // we actually just move the piece down if it doesn't collide
      my_current_piece = moved;
      my_last_blocks_placed = 0;
    }
    my_changed_flag = true;
    setChanged();
    notifyObservers();
  }

  /**
   * Rotate the current piece clockwise, if possible!
   */
  public void rotateClockwise() 
  {
    try
    {
      my_last_lines_removed = 0;
      my_last_blocks_placed = 0;
      my_changed_flag = false;
      final Piece moved = ((AbstractPiece) currentPiece()).clone();
      moved.rotateClockwise();
      if (!collides(moved)) 
      {
        my_current_piece = moved;
        my_changed_flag = true;
        setChanged();
      }
      notifyObservers();
    }
    catch (final CloneNotSupportedException e)
    {
      // this should never happen
      assert false;
    }
  }

  /**
   * Rotate the current piece counterclockwise, if possible!
   */
  public void rotateCounterclockwise() 
  {
    try
    {
      my_last_lines_removed = 0;
      my_last_blocks_placed = 0;
      my_changed_flag = false;
      final Piece moved = ((AbstractPiece) currentPiece()).clone();
      moved.rotateCounterclockwise();
      if (!collides(moved)) 
      {
        my_current_piece = moved;
        my_changed_flag = true;
        setChanged();
      }
      notifyObservers();
    }
    catch (final CloneNotSupportedException e)
    {
      // this should never happen
      assert false;
    }
  }


  /**
   * Drop the current piece!
   */
  public void drop() 
  {
    // replace the current piece with its projection to the bottom, then it's
    // just a normal moveDown.
    my_current_piece = projection();
    moveDown();
  }

  /**
   * @return What is your printable representation?
   */
  public /*@ non_null @*/ String toString() 
  {
    final StringBuffer sb = new StringBuffer();
    // we'll generate a String by going row by row down the list of rows;
    // we only render the visible parts of the board
    for (int y = height() - 1; 0 <= y; y--) 
    {
      sb.append(SIDE_BORDER_CHAR);
      for (int x = 0; x < width(); x++) 
      {
        if (color(new Point(x, y)) == null) 
        {
          sb.append(EMPTY_BLOCK_CHAR);
        } 
        else if (rowAt(y)[x] == null) 
        {
          sb.append(CURRENT_PIECE_BLOCK_CHAR);
        } 
        else 
        {
          sb.append(FROZEN_BLOCK_CHAR);
        }
      }
      sb.append(SIDE_BORDER_CHAR);
      sb.append('\n');
    }
    for (int x = 0; x <= width() + 1; x++) 
    {
      sb.append(BOTTOM_BORDER_CHAR);
    }
    sb.append('\n');
    return sb.toString();
  }

  // Helper Methods

  /*@ ensures
      \result <==>
      0 <= the_point.x() && the_point.x() < width() &&
      0 <= the_point.y() && the_point.y() < height() + ROWS_ABOVE_BOARD; @*/
  /**
   * @param the_point The point.
   * @return true if the specified point is within the boundaries of the board,
   * including the play area above the board, and false otherwise.
   */
  public /*@ pure @*/ boolean
  isWithinBoard(final /*@ non_null @*/ Point the_point) 
  {
    return 0 <= the_point.x() && the_point.x() < width() &&
           0 <= the_point.y() && the_point.y() < height() + ROWS_ABOVE_BOARD;
  }

  /**
   * Initializes some of the data structures.
   */
  private /*@ helper @*/ void initialize() 
  {
    my_current_piece = my_piece_generator.next();
    my_next_piece = my_piece_generator.next();
    my_last_lines_removed = 0;
    my_last_blocks_placed = 0;
    my_changed_flag = true;
    my_full_flag = false;
    my_row_list.clear();
    for (int i = 0; i < my_height + ROWS_ABOVE_BOARD; i++) 
    {
      my_row_list.add(new Color[my_width]);
    }
  }

  /**
   * Clears all full rows.
   */
  private /*@ helper @*/ void clearFullRows() 
  {
    final ListIterator<Color[]> iterator = my_row_list.listIterator();
    while (iterator.hasNext()) 
    {
      iterator.next();
      if (isFrozenRowFull(iterator.previousIndex())) 
      {
        iterator.remove();
        my_last_lines_removed = my_last_lines_removed + 1;
      }
    }
  }

  // Constraints (that are not in method contracts)

  // @constraint After a move or drop, no row has all blocks frozen.
  /*@ invariant (\forall int i; 0 <= i && i < height() + ROWS_ABOVE_BOARD;
                 (\exists int j; 0 <= j && j < width();
                  color(new Point(i, j)) == null)); @*/
}

