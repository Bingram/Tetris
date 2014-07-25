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
 * A piece shaped like the letter 'J'.
 *
 * @author Daniel M. Zimmerman (dmz@acm.org)
 * @version October 2012
 */
public class JPiece extends AbstractPiece 
{
  /**
   * The color of a J piece.
   */
  public static final Color COLOR = Color.BLUE;

  // @constraint Rotation 0 has positions ((0, 0), (1, 0), (1, 1), (1, 2)).
  /**
   * Rotation 0 of a J piece.
   */
  private static final Point[] ROTATION_ZERO =
    new Point[] {new Point(0, 0), new Point(1, 0),
                 new Point(1, 1), new Point(1, 2)};

  // @constraint Rotation 1 has positions ((0, 2), (0, 1), (1, 1), (2, 1)).
  /**
   * Rotation 1 of a J piece.
   */
  private static final Point[] ROTATION_ONE =
    new Point[] {new Point(0, 2), new Point(0, 1),
                 new Point(1, 1), new Point(2, 1)};

  // @constraint Rotation 2 has positions ((1, 0), (1, 1), (1, 2), (2, 2)).
  /**
   * Rotation 2 of a J piece.
   */
  private static final Point[] ROTATION_TWO =
    new Point[] {new Point(1, 0), new Point(1, 1),
                 new Point(1, 2), new Point(2, 2)};


  // @constraint Rotation 3 has positions ((0, 1), (1, 1), (2, 1), (2, 0)).
  /**
   * Rotation 3 of a J piece.
   */
  private static final Point[] ROTATION_THREE =
    new Point[] {new Point(0, 1), new Point(1, 1),
                 new Point(2, 1), new Point(2, 0)};

  /**
   * Constructs a J piece.
   */
  public JPiece() 
  {
    super(COLOR,
          Arrays.asList(new Rotation[] {new Rotation(ROTATION_ZERO),
                                        new Rotation(ROTATION_ONE),
                                        new Rotation(ROTATION_TWO),
                                        new Rotation(ROTATION_THREE)}));
  }

  // @constraint The color is blue.
  //@ invariant color().equals(Color.BLUE);

  // @constraint There are 4 rotations.
  //@ invariant rotations().size() == 4;
}
