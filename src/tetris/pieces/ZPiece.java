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
import java.util.Arrays;

import tetris.util.Point;

/**
 * A piece shaped like the letter 'Z'.
 * 
 * @author Daniel M. Zimmerman (dmz@acm.org)
 * @version October 2012
 */
public class ZPiece extends AbstractPiece 
{
  /**
   * The color of a Z piece.
   */
  public static final Color COLOR = Color.RED;

  // @constraint Rotation 0 has positions ((0, 1), (1, 1), (1, 0), (2, 0)).
  /**
   * Rotation 0 of a Z piece.
   */
  private static final Point[] ROTATION_ZERO =
      new Point[] {new Point(0, 1), new Point(1, 1), new Point(1, 0), new Point(2, 0)};

  // @constraint Rotation 1 has positions ((1, 0), (1, 1), (2, 1), (2, 2)).
  /**
   * Rotation 1 of a Z piece.
   */
  private static final Point[] ROTATION_ONE =
      new Point[] {new Point(1, 0), new Point(1, 1), new Point(2, 1), new Point(2, 2)};

  /**
   * Constructs a Z piece.
   */
  public ZPiece() 
  {
    super(COLOR, Arrays.asList(new Rotation[] 
    {new Rotation(ROTATION_ZERO), new Rotation(ROTATION_ONE)}));
  }

  // @constraint The color is red.
  //@ invariant color().equals(Color.RED);

  // @constraint There are 2 rotations.
  //@ invariant rotations().size() == 2;
}
