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
 * A piece shaped like the letter 'L'.
 *
 * @author Daniel M. Zimmerman (dmz@acm.org)
 * @version October 2012
 */
public class LPiece extends AbstractPiece 
{
  /**
   * The color of an L piece.
   */
  public static final Color COLOR = Color.ORANGE;

  // @constraint Rotation 0 has positions ((1, 2), (1, 1), (1, 0), (2, 0)).
  /**
   * Rotation 0 of an L piece.
   */
  private static final Point[] ROTATION_ZERO =
    new Point[] {new Point(1, 2), new Point(1, 1),
                 new Point(1, 0), new Point(2, 0)};

  // @constraint Rotation 1 has positions ((0, 0), (0, 1), (1, 1), (2, 1)).
  /**
   * Rotation 1 of an L piece.
   */
  private static final Point[] ROTATION_ONE =
    new Point[] {new Point(0, 0), new Point(0, 1),
                 new Point(1, 1), new Point(2, 1)};

  // @constraint Rotation 2 has positions ((0, 2), (1, 2), (1, 1), (1, 0)).
  /**
   * Rotation 2 of an L piece.
   */
  private static final Point[] ROTATION_TWO =
    new Point[] {new Point(0, 2), new Point(1, 2),
                 new Point(1, 1), new Point(1, 0)};

  // @constraint Rotation 3 has positions ((0, 1), (1, 1), (2, 1), (2, 2)).
  /**
   * Rotation 3 of an L piece.
   */
  private static final Point[] ROTATION_THREE =
    new Point[] {new Point(0, 1), new Point(1, 1),
                 new Point(2, 1), new Point(2, 2)};

  /**
   * Constructs an L piece.
   */
  public LPiece() 
  {
    super(COLOR,
          Arrays.asList(new Rotation[] {new Rotation(ROTATION_ZERO),
                                        new Rotation(ROTATION_ONE),
                                        new Rotation(ROTATION_TWO),
                                        new Rotation(ROTATION_THREE)}));
  }

  // @constraint The color is yellow.
  //@ invariant color().equals(Color.ORANGE);

  // @constraint There are 4 rotations.
  //@ invariant rotations().size() == 4;
}
