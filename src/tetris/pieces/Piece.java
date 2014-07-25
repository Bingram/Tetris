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
import java.util.List;

import tetris.util.Point;

/**
 * An interface for Tetris pieces that includes more functionality than
 * the basic rotation/movement/x/y commands.
 * 
 * @author Daniel M. Zimmerman
 * @version October 2012
 */
public interface Piece extends MutablePiece
{
  /**
   * The number of blocks in a piece.
   */
  int NUMBER_OF_BLOCKS = 4;
  
  /**
   * @return What are your rotations?
   */
  /*@ pure non_null */ List<Rotation> rotations();

  /**
   * @return What is your current set of blocks?
   */
  /*@ pure non_null */ Point[] blocks();

  /**
   * @return What is your origin?
   */
  /*@ pure non_null */ Point origin();

  /**
   * @return What is your color?
   */
  /*@ pure non_null */ Color color();

  /**
   * @param the_index The index.
   * @return What is the absolute position of block number the_index?
   */
  //@ requires 0 <= the_index && the_index <= blocks.length;
  //@ ensures \result.x() == origin().x() + blocks()[the_index].x();
  //@ ensures \result.y() == origin().y() + blocks()[the_index].y();
  /*@ pure non_null */ Point absolutePosition(int the_index);

  /**
   * Rotate clockwise!
   */
  //@ ensures origin().equals(\old(origin()));
  void rotateClockwise();

  /**
   * Rotate counterclockwise!
   */
  //@ ensures origin().equals(\old(origin()));
  void rotateCounterclockwise();
  
  /**
   * Set your origin to the_origin!
   *
   * @param the_origin The new origin.
   */
  //@ ensures \result.origin.equals(the_origin);
  //@ ensures Arrays.deepEquals(blocks(), \old(blocks()));
  void setOrigin(final /*@ non_null */ Point the_origin);
}
