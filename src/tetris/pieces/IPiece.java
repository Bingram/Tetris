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
 * A piece shaped like the letter 'I'.
 *
 * @author Daniel M. Zimmerman (dmz@acm.org)
 * @version October 2012
 */
public class IPiece extends AbstractPiece 
{
  /**
   * The color of an I piece.
   */
  public static final Color COLOR = Color.CYAN.darker();

  // @constraint Rotation 0 has positions ((0, 1), (1, 1), (2, 1), (3, 1)).
  /**
   * Rotation 0 of an I piece.
   */
  private static final Point[] ROTATION_ZERO =
    new Point[] {new Point(0, 1), new Point(1, 1),
                 new Point(2, 1), new Point(3, 1)};

  // @constraint Rotation 1 has positions ((2, 3), (2, 2), (2, 1), (2, 0)).
  /**
   * Rotation 1 of an I piece.
   */
  private static final Point[] ROTATION_ONE =
    new Point[] {new Point(2, 3), new Point(2, 2),
                 new Point(2, 1), new Point(2, 0)};

  /**
   * Constructs an I piece.
   */
  public IPiece() 
  {
    super(COLOR,
          Arrays.asList(new Rotation[] {new Rotation(ROTATION_ZERO),
                                        new Rotation(ROTATION_ONE)}));
  }

  // @constraint The color is cyan.
  //@ invariant color().equals(Color.CYAN);

  // @constraint There are 2 rotations.
  //@ invariant rotations().size() == 2;
}
