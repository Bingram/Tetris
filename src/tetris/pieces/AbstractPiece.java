/*
 * An implementation of the classic game "Tetris".
 * 
 * @author "Daniel M. Zimmerman (dmz@acm.org)"
 * @module "TCSS 305"
 * @creation_date "July 2008"
 * @last_updated_date "October 2012"
 * @keywords "Tetris", "game"
 */

package tetris.pieces;

import java.awt.Color;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import tetris.util.Point;

/**
 * A set of rotations, with position and color information.
 *
 * @author Daniel M. Zimmerman (dmz@acm.org)
 * @version October 2012
 */
public abstract class AbstractPiece implements Piece, Cloneable
{
  // Static Fields

  /**
   * The character used in the String representation to represent an
   * empty block.
   */
  private static final char EMPTY_BLOCK_CHAR = ' ';

  /**
   * The character used in the String representation to represent a
   * full block.
   */
  private static final char FULL_BLOCK_CHAR = '+';

  // Instance Fields

  /**
   * The current rotation number.
   */
  private int my_current_rotation;

  /**
   * The color.
   */
  private final /*@ non_null @*/ Color my_color;
  
  /**
   * The list of rotations.
   */
  private final /*@ non_null @*/ List<Rotation> my_rotations;

  /**
   * The origin.
   */
  private /*@ non_null @*/ Point my_origin;

  // Constructor

  /*@ requires (\forall Rotation r; the_rotations.contains(r);
                r.blocks.length == NUMBER_OF_BLOCKS); @*/
  /*@ requires the_rotations.size() == 1 || the_rotations.size() == 2 ||
               the_rotations.size() == 4; @*/
  //@ ensures color() == the_color;
  //@ ensures rotations().equals(the_rotations);
  //@ ensures origin().x() == 0 && origin().y() == 0;
  /**
   * These are your rotations! This is your color!
   *
   * @param the_color The color.
   * @param the_rotations The rotations.
   */
  public AbstractPiece(final /*@ non_null @*/ Color the_color,
               final /*@ non_null @*/ List<Rotation> the_rotations) 
  {
    my_color = the_color; // colors are immutable
    final List<Rotation> temp =
      Collections.unmodifiableList(new ArrayList<Rotation>(the_rotations));
    my_rotations = temp;
    my_current_rotation = 0;
    my_origin = new Point(0, 0);
  }

  // Queries

  /* (non-Javadoc)
   * @see tetris.entities.pieces.Piece#rotations()
   */
  @Override
  public /*@ pure non_null */ List<Rotation> rotations() 
  {
    return my_rotations;
  }

  /* (non-Javadoc)
   * @see tetris.entities.pieces.Piece#blocks()
   */
  @Override
  public /*@ pure non_null */ Point[] blocks() 
  {
    return ((Rotation) rotations().get(my_current_rotation)).blocks();
  }

  /* (non-Javadoc)
   * @see tetris.entities.pieces.Piece#origin()
   */
  @Override
  public /*@ pure non_null */ Point origin() 
  {
    return my_origin;
  }

  /**
   * @return What is your x-coordinate?
   */
  //@ ensures \result == origin().x();
  public /*@ pure */ int x() 
  {
    return my_origin.x();  
  }

  /**
   * @return What is your y-coordinate?
   */
  //@ ensures \result == origin().y();
  public /*@ pure */ int y() 
  {
    return my_origin.y();  
  }
  
  /* (non-Javadoc)
   * @see tetris.entities.pieces.Piece#color()
   */
  @Override
  public /*@ pure non_null */ Color color()
  {
    return my_color;
  }

  /* (non-Javadoc)
   * @see tetris.entities.pieces.Piece#absolutePosition(int)
   */
  //@ requires 0 <= the_index && the_index <= blocks.length;
  //@ ensures \result.x() == origin().x() + blocks()[the_index].x();
  //@ ensures \result.y() == origin().y() + blocks()[the_index].y();
  @Override
  public /*@ pure non_null */ Point absolutePosition(final int the_index) 
  {
    return new Point(origin().x() + blocks()[the_index].x(),
                     origin().y() + blocks()[the_index].y());
  }

  /**
   * Move left!
   */
  //@ ensures origin().x() == \old(origin().x() - 1);
  //@ ensures origin().y() == \old(origin().y());
  //@ ensures Arrays.deepEquals(blocks(), \old(blocks()));
  public void moveLeft() 
  {
    my_origin = new Point(my_origin.x() - 1, my_origin.y());
  }


  /**
   * Move right!
   */
  //@ ensures origin().x() == \old(origin().x() + 1);
  //@ ensures origin().y() == \old(origin().y());
  //@ ensures Arrays.deepEquals(blocks(), \old(blocks()));
  public void moveRight() 
  {
    my_origin = new Point(my_origin.x() + 1, my_origin.y());
  }

  /**
   * Move down!
   */
  //@ ensures origin().x() == \old(origin().x());
  //@ ensures origin().y() == \old(origin().y() - 1);
  //@ ensures Arrays.deepEquals(blocks(), \old(blocks()));
  public void moveDown() 
  {
    my_origin = new Point(my_origin.x(), my_origin.y() - 1);
  }

  /**
   * Rotate counterclockwise!
   */
  // duplicate method necessary for MutablePiece interface.
  //@ ensures origin().equals(\old(origin()));
  public void rotate() 
  {
    rotateCounterclockwise();
  }
  
  /* (non-Javadoc)
   * @see tetris.entities.pieces.Piece#rotateClockwise()
   */
  //@ ensures origin().equals(\old(origin()));
  @Override
  public void rotateClockwise() 
  {
    my_current_rotation = (my_current_rotation + 1) % rotations().size();
  }

  /* (non-Javadoc)
   * @see tetris.entities.pieces.Piece#rotateCounterclockwise()
   */
  //@ ensures origin().equals(\old(origin()));
  @Override
  public void rotateCounterclockwise() 
  {
    my_current_rotation =
        (my_current_rotation + rotations().size() - 1) % rotations().size();
  }

  /**
   * Set your origin to the_origin!
   *
   * @param the_origin The new origin.
   */
  //@ ensures \result.origin.equals(the_origin);
  //@ ensures Arrays.deepEquals(blocks(), \old(blocks()));
  public void setOrigin(final /*@ non_null */ Point the_origin) 
  {
    my_origin = the_origin;
  }
 
  // Clone Method

  /**
   * {@inheritDoc}
   */
  public /*@ pure non_null */ Piece clone()
    throws CloneNotSupportedException 
  {
    // even though the object is mutable, the color and rotation list are final; 
    // ints are primitive types, and Points are immutable, so this
    // is sufficient to clone the object.
    return (Piece) super.clone();
  }

  /**
   * {@inheritDoc}
   */
  public /*@ pure */ boolean equals(final /*@ nullable @*/ Object the_other) 
  {
    boolean result = this == the_other;
    if (!result && the_other != null && the_other.getClass() == getClass()) 
    {
      final Piece other_piece = (Piece) the_other;
      result = other_piece.color().equals(color());
      result = result && other_piece.origin().equals(origin());
      result =
        result && Arrays.deepEquals(other_piece.blocks(), blocks());
      for (int i = 0; result && i < rotations().size(); i++) 
      {
        result = result &&
                 other_piece.rotations().get(i).equals(rotations().get(i));
      }
    }
    return result;
  }

  /**
   * {@inheritDoc}
   */
  public /*@ pure */ int hashCode() 
  {
    return my_color.hashCode() + my_origin.hashCode() +
           my_current_rotation; 
  }

  /**
   * @return What is your printable representation?
   */
  public /*@ non_null @*/ String toString() 
  {
    final StringBuffer sb = new StringBuffer();
    // we'll generate a String by going line by line and checking for blocks
    for (int y = NUMBER_OF_BLOCKS - 1; 0 <= y; y--) 
    {
      for (int x = 0; x < NUMBER_OF_BLOCKS; x++) 
      {
        for (int i = 0; i < NUMBER_OF_BLOCKS; i++) 
        {
          final Point pos = blocks()[i];
          if (pos.x() == x && pos.y() == y) 
          {
            sb.append(FULL_BLOCK_CHAR);
          } 
          else 
          {
            sb.append(EMPTY_BLOCK_CHAR);
          }
        }
      }
      sb.append('\n');
    }
    sb.append("\nOrigin: ");
    sb.append(origin());
    sb.append('\n');
    return sb.toString();
  }
}
