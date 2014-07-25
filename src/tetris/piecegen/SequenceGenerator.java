/*
 * An implementation of the classic game "Tetris".
 * 
 * @author "Daniel M. Zimmerman (dmz@acm.org)"
 * @module "TCSS 305"
 * @creation_date "July 2008"
 * @last_updated_date "October 2012"
 * @keywords "Tetris", "game"
 */

package tetris.piecegen;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import tetris.pieces.AbstractPiece;
import tetris.pieces.OPiece;
import tetris.pieces.Piece;

/**
 * A piece generator that repeatedly cycles through a specified
 * sequence of pieces.
 *
 * @author Daniel M. Zimmerman (dmz@acm.org)
 * @version 29 July 2008
 */
public class SequenceGenerator implements PieceGenerator 
{
  // Instance Fields

  /**
   * The sequence of pieces used by this piece generator.
   */
  private final /*@ non_null @*/ List<Piece> my_sequence;

  /**
   * The current index in the sequence of pieces.
   */
  private int my_index;

  // Constructors

  /**
   * Constructs a new SequenceGenerator using the specified sequence.
   *
   * @param the_sequence The sequence.
   */
  //@ requires 0 < the_sequence.size();
  public SequenceGenerator
  (final /*@ non_null @*/ List<AbstractPiece> the_sequence) 
  {
    my_sequence = Collections.unmodifiableList(new ArrayList<Piece>(the_sequence));
    my_index = 0;
  }

  // Instance Methods

  /**
   * {@inheritDoc}
   */
  public /*@ non_null @*/ Piece next() 
  {
    Piece result;
    try 
    {
      result = ((AbstractPiece) my_sequence.get(my_index)).clone();
      my_index = (my_index + 1) % my_sequence.size();
    } 
    catch (final CloneNotSupportedException e) 
    {
      // this should never happen
      //@ assert false;
      assert false;
      result = new OPiece();
    }
    return result;
  }
}
