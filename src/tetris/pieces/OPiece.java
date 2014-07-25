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
 * A piece shaped like the letter 'O'.
 *
 * @author Daniel M. Zimmerman (dmz@acm.org)
 * @version October 2012
 */
public class OPiece extends AbstractPiece 
{
  /**
   * The color of an O piece.
   */
  public static final Color COLOR = Color.YELLOW.darker();

  // @constraint Rotation 0 has positions ((1, 1), (1, 2), (2, 1), (2, 2)).
  /**
   * Rotation 0 of an O piece.
   */
  private static final Point[] ROTATION_ZERO =
    new Point[] {new Point(1, 1), new Point(1, 2),
                 new Point(2, 1), new Point(2, 2)};

  /**
   * Constructs an O piece.
   */
  public OPiece() 
  {
    super(COLOR,
          Arrays.asList(new Rotation[] {new Rotation(ROTATION_ZERO)}));
  }

  // @constraint The color is yellow.
  //@ invariant color().equals(Color.YELLOW);

  // @constraint There is 1 rotation.
  //@ invariant rotations().size() == 1;
}
