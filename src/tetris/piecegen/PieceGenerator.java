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

import tetris.pieces.Piece;

/**
 * A generator for Tetris pieces.
 *
 * @author Daniel M. Zimmerman (dmz@acm.org)
 * @version October 2012
 */
public interface PieceGenerator 
{
  /**
   * @return the next piece.
   */
  /*@ non_null @*/ Piece next();
}
