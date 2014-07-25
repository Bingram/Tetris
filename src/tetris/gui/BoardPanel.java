package tetris.gui;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.event.ActionEvent;
import java.awt.event.KeyEvent;
import javax.swing.AbstractAction;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.KeyStroke;
import tetris.Board;
import tetris.util.Point;

/**
 * Creates a board panel which contains piece movement
 * and key controls for tetris game.
 * 
 * @author Brian Ingram
 * @version 11/25/2012
 */
@SuppressWarnings("serial") 
public class BoardPanel extends JPanel
{
  /**
   * Sets how many columns are used on board.
   */
  private static final int GRID_X = 10;
  
  /**
   * Number of rows, double the number of columns.
   */
  private static final int GRID_Y = GRID_X * 2;
  
  /**
   * Constant for calculating block paint position in
   * y-coordinate.
   */
  private static final int GRID_CALC = 19;
  
  /**
   * Constant for number of blocks in a piece.
   */
  private static final int NUM_BLKS = 4;
  

  
  /**
   * Default dimension of the game board.
   */
  private static final Dimension WINDOW = 
                        new Dimension(300, 600);
  /**
   * String constant for clearing keys.
   */
  private static final String CLEAR = "none";
  
  /**
   * String constant for game over message.
   */
  private static final String GAME_OVER = "GAME OVER";
  
  /**
   * Default BG color.
   */
  private final Color my_bg = Color.WHITE;
  
  /**
   * Boolean value for mirror mode play.
   * Board displays mirrored while true.
   */
  private Boolean my_mirror_mode = false;
  
  /**
   * The game board being used for this game.
   */
  private Board my_board;
  
  /**
   * Constructor for board panel.
   * Creates new board with number of rows, columns and 
   * seed number for random pieces.
   * 
   * @param the_board Board object this panel observes
   */
  public BoardPanel(final Board the_board)
  {
    super();
    my_board = the_board;
    
    setupBoard();
  }
  
  /**
   * Sets up the board, actions and keys to actions.
   */
  private void setupBoard()
  {
    setBackground(my_bg);
    setPreferredSize(WINDOW);
    setSize(WINDOW);
  }
  
  /**
   * Uses inputmap/actionmap to map actions to specific keys.
   */
  public void createKeys()
  {
    /**
     * Inner class for move left action.
     * @author Brian Ingram
     * @version FINAL
     */
    class LeftAction extends AbstractAction
    {
      @Override
      public void actionPerformed(final ActionEvent the_event)
      {
        my_board.moveLeft();
        repaint();
      }
    }
    
    /**
     * Inner class for move right action.
     * @author Brian Ingram
     * @version FINAL
     */
    class RightAction extends AbstractAction
    {
      @Override
      public void actionPerformed(final ActionEvent the_event)
      {
        my_board.moveRight();
        repaint();
      }
    }
    
    /**
     * Inner class for move down action.
     * @author Brian Ingram
     * @version FINAL
     */
    class DownAction extends AbstractAction
    {
      @Override
      public void actionPerformed(final ActionEvent the_event)
      {
        my_board.moveDown();
        repaint();
      }
    }
    
    /**
     * Inner class for rotate action.
     * @author Brian Ingram
     * @version FINAL
     */
    class RotateAction extends AbstractAction
    {
      @Override
      public void actionPerformed(final ActionEvent the_event)
      {
        my_board.rotateClockwise();
        repaint();
      }
    }
    
    /**
     * Inner class for quick drop action.
     * @author Brian Ingram
     * @version FINAL
     */
    class DropAction extends AbstractAction
    {

      @Override
      public void actionPerformed(final ActionEvent the_event)
      {
        my_board.drop();
        repaint();
      }
      
    }
    
    getActionMap().put(TetrisKey.LEFT, new LeftAction());
    getActionMap().put(TetrisKey.RIGHT, new RightAction());
    getActionMap().put(TetrisKey.DOWN, new DownAction());
    getActionMap().put(TetrisKey.ROTATE, new RotateAction());
    getActionMap().put(TetrisKey.DROP, new DropAction());

  }
  
  /**
   * Matches actions to keys.
   * @param the_controls string to switch controls.
   */
  public void setKeys(final String the_controls)
  {
    if ("LEFT".equals(the_controls))
    {
      getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_A, 0), TetrisKey.LEFT);
      getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_D, 0), TetrisKey.RIGHT);
      getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_S, 0), TetrisKey.DOWN);
      getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_W, 0), TetrisKey.ROTATE);
      getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_SPACE, 0), TetrisKey.DROP);
    }
    else if ("RIGHT".equals(the_controls))
    {
      getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_LEFT, 0), TetrisKey.LEFT);
      getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_RIGHT, 0), TetrisKey.RIGHT);
      getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_DOWN, 0), TetrisKey.DOWN);
      getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_UP, 0), TetrisKey.ROTATE);
      getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_SPACE, 0), TetrisKey.DROP);
    }
  }
  
  /**
   * Enumeration to match keys to actions.
   * @author Brian Ingram
   * @version FINAL
   */
  public enum TetrisKey
  {
    /**
     * Enum for left.
     */
    LEFT,
    /**
     * Enum for right.
     */
    RIGHT,
    /**
     * Enum for down.
     */
    DOWN,
    /**
     * Enum for rotate.
     */
    ROTATE,
    /**
     * Enum for quick drop.
     */
    DROP;
  }
  
  /**
   * Disconnects keys from game by setting map value to "none".
   */
  public void clearKeys()
  {
    getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_A, 0), CLEAR);
    getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_D, 0), CLEAR);
    getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_S, 0), CLEAR);
    getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_W, 0), CLEAR);
    getInputMap().put(KeyStroke.getKeyStroke(KeyEvent.VK_SPACE, 0), CLEAR);
  }
  
  /**
   * Sets the boolean value used to control
   * paintcomponent logic. If true, mirrors the
   * board upside-down and left > right.
   * 
   * @param the_bool boolean value
   */
  public void setMirror(final Boolean the_bool)
  {
    my_mirror_mode = the_bool;
    repaint();
  }
  
  /**
   * Sets new board for panel, establish the keys and repaint.
   * @param the_board new game board
   */
  public void newGame(final Board the_board)
  {
    my_board = the_board;
    createKeys();
    repaint();
  }

  /**
   * Paints the grid background in black, all currently frozen blocks and current piece.
   * @param the_graphics graphics to paint
   */
  public void paintComponent(final Graphics the_graphics)
  {
    super.paintComponent(the_graphics);
    final Graphics2D g2d = (Graphics2D) the_graphics;

    final int ratio = this.getHeight() / GRID_Y;
    
    g2d.setColor(Color.WHITE);
    g2d.drawRect(0, 0, getWidth(), getHeight());
    
    if (my_mirror_mode)
    {
      normalPaint(g2d, ratio);
    }
    else
    {
      mirrorPaint(g2d, ratio);
    }

  }
  
  /**
   * Logic for normal painting of game board.
   * @param the_graphics graphics2d
   * @param the_ratio ratio of height to rows
   */
  private void normalPaint(final Graphics2D the_graphics, final int the_ratio)
  {
    /**
     * Paints black grid using my_ratio to calculate points
     * and side lengths. Then paints block 1px smaller on sides
     * using present color at row and column position, i & j 
     * respectively.
     */
    for (int i = GRID_Y - 1; i >= 0; i--) 
    {
      final Color[] colors = my_board.rowAt(i);
      
      for (int j = 0; j < GRID_X; j++)
      {
        the_graphics.setColor(my_board.currentPiece().color());

        the_graphics.drawRect(j * the_ratio, (GRID_CALC - i) * 
                              the_ratio, the_ratio - 1, the_ratio - 1);
        
        if (colors[j] == null)
        {
          the_graphics.setColor(Color.BLACK);
        }
        else
        {
          the_graphics.setColor(colors[j]);
        }
        
        the_graphics.fillRect(j * the_ratio, (GRID_CALC - i) * 
                              the_ratio, the_ratio - 1, the_ratio - 1);
      }
    }
    
    /**
     * Paints current piece using filled rectangles using.
     */
    
    for (int i = 0; i < NUM_BLKS; i++) 
    {
      final Point block_pos = my_board.currentPiece().absolutePosition(i);
      the_graphics.setColor(Color.BLACK);
      the_graphics.drawRect((block_pos.x()) * the_ratio, (GRID_CALC - block_pos.y()) * 
                            the_ratio, the_ratio - 1, the_ratio - 1);
      if (block_pos.y() < GRID_Y)
      {
        the_graphics.setColor(my_board.currentPiece().color());
        the_graphics.fillRect((block_pos.x()) * the_ratio, (GRID_CALC - block_pos.y()) * 
                              the_ratio, the_ratio - 1, the_ratio - 1);
      }
    }
  }
  
  /**
   * Logic for mirror painting of game board.
   * @param the_graphics graphics2d
   * @param the_ratio ratio of height to rows
   */
  private void mirrorPaint(final Graphics2D the_graphics, final int the_ratio)
  {
    for (int i = 0; i < GRID_Y; i++) 
    {
      final Color[] colors = my_board.rowAt(i);
      
      for (int j = 0; j < GRID_X; j++)
      {
        the_graphics.setColor(my_board.currentPiece().color());

        the_graphics.drawRect(j * the_ratio, i * the_ratio, 
                                  the_ratio - 1, the_ratio - 1);
        
        if (colors[j] == null)
        {
          the_graphics.setColor(Color.BLACK);
        }
        else
        {
          the_graphics.setColor(colors[j]);
        }
        
        the_graphics.fillRect(j * the_ratio, i * the_ratio, 
                                the_ratio - 1, the_ratio - 1);
      }
    }
    
    the_graphics.setColor(my_board.currentPiece().color());
    for (int i = 0; i < NUM_BLKS; i++) 
    {
      final Point block_pos = my_board.currentPiece().absolutePosition(i);
      the_graphics.setColor(Color.BLACK);
      the_graphics.drawRect((block_pos.x()) * the_ratio, block_pos.y() * the_ratio,
                            the_ratio - 1, the_ratio - 1);
      if (block_pos.y() < GRID_Y)
      {
        the_graphics.setColor(my_board.currentPiece().color());
        the_graphics.fillRect((block_pos.x()) * the_ratio, block_pos.y() * the_ratio,
                              the_ratio - 1, the_ratio - 1);
      }
        
    }
  }
  
  /**
   * Displays message of game over.
   * Clears key values so they do nothing.
   */
  public void gameOver()
  {
    clearKeys();
    JOptionPane.showMessageDialog(this, GAME_OVER);
  }
    
  
}
