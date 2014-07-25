/*
 * An implementation of the classic game "Tetris".
 * Class Point.
 * 
 * @author "Daniel M. Zimmerman (dmz@acm.org)"
 * @module "TCSS 305"
 * @creation_date "July 2008"
 * @last_updated_date "July 2008"
 * @keywords "Tetris", "game"
 */

package tetris.util;

/**
 * The location of a single block on the board.
 *
 * @author Daniel M. Zimmerman (dmz@acm.org)
 * @version 29 July 2008
 */
public class Point 
{
  // partially subsumes BLOCK (position)
  // Instance Fields
  /**
   * The x-coordinate.
   */
  private final int my_x;

  // @constraint The x-coordinate and y-coordinate are finite.
  // @constraint Points are immutable.
  /*@ public model int x;
      public constraint \old(x) == x;
      private represents x = my_x; @*/

  /**
   * The y-coordinate.
   */
  private final int my_y;

  // @constraint The x-coordinate and y-coordinate are finite.
  // @constraint Points are immutable.
  /*@ public model int y;
      public constraint \old(y) == y;
      private represents y = my_y; @*/

  // Constructor
  /**
   * This is your x-coordinate! This is your y-coordinate!
   *
   * @param the_x The x-coordinate.
   * @param the_y The y-coordinate.
   */
  //@ ensures x == the_x;
  //@ ensures y == the_y;
  public /*@ pure @*/ Point(final int the_x, final int the_y) 
  {
    my_x = the_x;
    my_y = the_y;
  }

  // Queries

  /**
   * @return What is your x-coordinate?
   */
  //@ ensures \result == x;
  public /*@ pure @*/ int x() 
  {
    return my_x;
  }

  /**
   * @return What is your y-coordinate?
   */
  //@ ensures \result == y;
  public /*@ pure @*/ int y() 
  {
    return my_y;
  }

  // Object Methods

  /*@ also public behavior
      requires the_other != null && \typeof(the_other) == \typeof(this);
      ensures \result <==>
              ((Point) the_other).x == x && ((Point) the_other).y == y; @*/
  /*@ also public behavior
      requires the_other == null || \typeof(the_other) != \typeof(this);
      ensures !\result; @*/
  /**
   * {@inheritDoc}
   */
  public /*@ pure @*/ boolean equals(final /*@ nullable @*/ Object the_other)
  {
    boolean result = this == the_other;
    if (!result && the_other != null && the_other.getClass() == getClass()) 
    {
      result = ((Point) the_other).x() == x() &&
               ((Point) the_other).y() == y();
    }
    return result;
  }

  /**
   * {@inheritDoc}
   */
  //@ public represents theHashCode = x + y;
  public /*@ pure @*/ int hashCode() 
  {
    return x() + y();
  }
}
