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
 * A piece shaped like the letter 'S'.
 *
 * @author Daniel M. Zimmerman (dmz@acm.org)
 * @version October 2012
 */
public class SPiece extends AbstractPiece 
{
  /**
   * The color of an S piece.
   */
  public static final Color COLOR = Color.GREEN.darker();

  // @constraint Rotation 0 has positions ((0, 0), (1, 0), (1, 1), (2, 1)).
  /**
   * Rotation 0 of an S piece.
   */
  private static final Point[] ROTATION_ZERO =
    new Point[] {new Point(0, 0), new Point(1, 0),
                 new Point(1, 1), new Point(2, 1)};

  // @constraint Rotation 1 has positions ((1, 2), (1, 1), (2, 1), (2, 0)).

  /**
   * Rotation 1 of an S piece.
   */
  private static final Point[] ROTATION_ONE =
    new Point[] {new Point(1, 2), new Point(1, 1),
                 new Point(2, 1), new Point(2, 0)};

  /**
   * Constructs an S piece.
   */
  public SPiece() 
  {
    super(COLOR,
          Arrays.asList(new Rotation[] {new Rotation(ROTATION_ZERO),
                                        new Rotation(ROTATION_ONE)}));
  }

  // @constraint The color is green.
  //@ invariant color().equals(Color.GREEN);

  // @constraint There are 2 rotations.
  //@ invariant rotations().size() == 2;
}
