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

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import tetris.pieces.IPiece;
import tetris.pieces.JPiece;
import tetris.pieces.LPiece;
import tetris.pieces.OPiece;
import tetris.pieces.Piece;
import tetris.pieces.SPiece;
import tetris.pieces.TPiece;
import tetris.pieces.ZPiece;
import tetris.util.Point;

/**
 * A piece generator that uses random numbers to generate pieces based
 * on an initial seed value; it follows the Tetris convention of putting
 * the seven pieces in random order, giving them all, then repeating
 * as necessary.
 *
 * @author Daniel M. Zimmerman (dmz@acm.org)
 * @version October 2012
 */
public class RandomGenerator implements PieceGenerator 
{
  // Instance Fields
  /**
   * The random number generator used by this piece generator.
   */
  private final /*@ non_null @*/ Random my_random;
 
  /**
   * The origin to use for random pieces.
   */
  private final /*@ non_null @*/ Point my_origin;

  /**
   * The piece list, used to keep track of each "set" of pieces.
   */
  private final /*@ non_null @*/ List<Piece> my_piece_list;

  // Constructors

  /**
   * Constructs a new RandomGenerator with the specified random seed
   * and the specified piece origin.
   *
   * @param the_seed The random seed.
   * @param the_origin The origin.
   */
  public RandomGenerator(final long the_seed,
                         final /*@ non_null @*/ Point the_origin) 
  {
    my_random = new Random(the_seed);
    my_origin = the_origin;
    my_piece_list = new ArrayList<Piece>();
    fillPieceList();
  }

  // Instance Methods

  /**
   * {@inheritDoc}
   */
  public /*@ non_null @*/ Piece next() 
  {
    final int choice = my_random.nextInt(my_piece_list.size());
    final Piece result = my_piece_list.get(choice);
    my_piece_list.remove(choice);
    if (my_piece_list.isEmpty()) 
    {
      fillPieceList();
    }
    return result;
  }

  /**
   * Populates the piece list with 28 pieces, four of each type.
   */
  private /*@ helper @*/ void fillPieceList() 
  {
    final Piece[] pieces = new Piece[]
    {new IPiece(), new JPiece(), new LPiece(), new OPiece(),
     new SPiece(), new TPiece(), new ZPiece(),
     new IPiece(), new JPiece(), new LPiece(), new OPiece(),
     new SPiece(), new TPiece(), new ZPiece(),
     new IPiece(), new JPiece(), new LPiece(), new OPiece(),
     new SPiece(), new TPiece(), new ZPiece(),
     new IPiece(), new JPiece(), new LPiece(), new OPiece(),
     new SPiece(), new TPiece(), new ZPiece()};
    for (Piece p : pieces) 
    {
      p.setOrigin(my_origin);
      my_piece_list.add(p);
    }
  }
}
