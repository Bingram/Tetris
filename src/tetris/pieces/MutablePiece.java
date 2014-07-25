/*
 * TCSS 305 - Autumn 2012
 * Project Tetris
 */

package tetris.pieces;

/**
 * This interface defines the required operations of mutable Tetris
 * pieces. Your pieces will implement either this interface or the
 * MutablePiece interface, <i>but not both</i>. 
 * 
 * @author Daniel M. Zimmerman
 * @version Autumn 2012
 */
public interface MutablePiece
{
  /** 
   * Moves this piece one space to the left. 
   */
  void moveLeft();

  /** 
   * Moves this piece one space to the right. 
   */
  void moveRight();

  /** 
   * Moves this piece one space down. 
   */
  void moveDown();

  /** 
   * Rotates this piece one quarter turn counter-clockwise. 
   */
  void rotate();

  /**
   * @return the x coordinate of this piece.
   */
  int x();

  /**
   * @return the y coordinate of this piece.
   */
  int y();
}
