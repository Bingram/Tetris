package tetris.gui;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.util.Observable;
import java.util.Observer;
import javax.swing.JPanel;

import tetris.Board;
import tetris.util.Point;

/**
 * Creates a panel that displays the next piece.
 * @author Brian Ingram
 * @version Part 3 Final
 */
@SuppressWarnings("serial")
public class NextPiecePanel extends JPanel implements Observer
{
  /**
   * Number of blocks in piece.
   */
  private static final int NUM_BLKS = 4;
 
  /**
   * Constant for drawing sides of each block.
   */
  private static final int CUBE = 20;
  
  /**
   * Board this panel listens to.
   */
  private Board my_board;

  /**
   * Constructs panel and passes current board and panel.
   * Gets next piece from board, and current ratio from panel.
   * 
   * @param the_board game board
   */
  public NextPiecePanel(final Board the_board)
  {
    super();
    setFocusable(false);
    my_board = the_board;
    my_board.addObserver(this);

    setBackground(Color.WHITE);
    setPreferredSize(new Dimension(CUBE * 4, CUBE * 4));
    setSize(CUBE * 4, CUBE * 4);
  }
  
  /**
   * Sets new board and repaints this panel.
   * @param the_board new game board
   */
  public void newGame(final Board the_board)
  {
    my_board = the_board;
    
    repaint();
  }
  
  /**
   * Paints the next piece in static grid.
   * @param the_graphics graphics to paint
   */
  public void paintComponent(final Graphics the_graphics)
  {
    super.paintComponent(the_graphics);
    final Graphics2D g2d = (Graphics2D) the_graphics;
       
    final Point[] block_pos = my_board.nextPiece().blocks();
    for (int i = 0; i < NUM_BLKS; i++) 
    {
      block_pos[i].x();      
      g2d.setColor(my_board.nextPiece().color());
      g2d.fillRect(block_pos[i].x()  * CUBE, block_pos[i].y()  * CUBE, 
                   CUBE - 1, CUBE - 1);
    }
  }

  @Override
  public void update(final Observable the_arg0, final Object the_arg1)
  {
    repaint();
  }

}
