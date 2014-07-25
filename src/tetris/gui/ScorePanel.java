package tetris.gui;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Font;
import java.util.Observable;
import java.util.Observer;

import javax.swing.BoxLayout;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JProgressBar;

import tetris.Board;

/**
 * Creates a panel that displays the next piece.
 * @author Brian Ingram
 * @version Part 3 Final
 */
@SuppressWarnings("serial")
public class ScorePanel extends JPanel implements Observer
{  
  /**
   * Constant used for scoring calculations.
   */
  private static final int GRID = 10;
  
  /**
   * Board this panel listens to.
   */
  private Board my_board;
  
  /**
   * Graphical progress bar for level.
   */
  private final JProgressBar my_progress;
  
  /**
   * Current total score.
   */
  private int my_total_score;

  /**
   * Label for displaying score.
   */
  private final JLabel my_score;
  
  /**
   * Label for displaying current level.
   */
  private final JLabel my_lvl;
  
  /**
   * Total number of lines cleared in game.
   */
  private int my_lines_cleared;
  
  /**
   * Sets font for score display.
   */
  private final Font my_score_font;
  
  /**
   * Sets font for level display.
   */
  private final Font my_lvl_font;

  /**
   * Rolling counter for progress bar.
   * Incremented once for each line cleared,
   * after 10 it resets to 0.
   */
  private int my_lvl_lines;
  
  /**
   * Constructs panel and passes current board and panel.
   * Gets next piece from board, and current ratio from panel.
   * 
   * @param the_board game board
   */
  public ScorePanel(final Board the_board)
  {
    super();
    my_board = the_board;
    
    my_progress = new JProgressBar();
    my_score = new JLabel();
    my_lvl = new JLabel();
    
    my_score_font = new Font("Arial", Font.BOLD, 14);
    my_lvl_font = new Font("Arial", Font.PLAIN, 12);
    
    setup();
  }
  
  /**
   * Does the basic setup on the score panel.
   * Sets font, observable, size and components.
   */
  private void setup()
  {
    my_score.setFont(my_score_font);
    my_lvl.setFont(my_lvl_font);
    my_board.addObserver(this);
    my_total_score = 0;
    my_score.setText("SCORE| " + my_total_score);
    my_lvl.setText("LVL " + my_lines_cleared / GRID);
    add(my_score);
    add(my_lvl);
    add(my_progress);
    setFocusable(false);
    setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));
    setBackground(Color.WHITE);
    setPreferredSize(new Dimension(40, 50));
    setSize(40, 50); 
  }

  /**
   * Changes board to new one passed in.
   * Resets score to 0.
   * @param the_board new game board
   */
  public void newGame(final Board the_board)
  {
    my_board = the_board;
    setup();    
  }
  
  /**
   * Add the_score to current total.
   * @param the_score int to add
   */
  public void addScore(final int the_score)
  {
    my_total_score += the_score;
  }
  
  /**
   * Returns total lines cleared.
   * @return my_lines_cleared
   */
  public int getLines()
  {
    return my_lines_cleared;
  }
  
  /**
   * Returns the current level as int.
   * @return int current level
   */
  public int getLvl()
  {
    return my_lines_cleared / GRID;
  }
  
  @Override
  public void update(final Observable the_board, final Object the_arg)
  {
    
    my_lines_cleared += my_board.lastLinesRemoved();
    
    if (my_lvl_lines == GRID)
    {
      my_progress.setValue(0);
      my_lvl_lines = 0;
    }
    else
    {
      my_progress.setValue(my_lvl_lines * GRID);
    }
    
    if (my_board.lastLinesRemoved() > 1)
    {
      my_total_score += my_board.lastLinesRemoved() * GRID;
      my_lvl_lines += my_board.lastLinesRemoved();
    }
    else if (my_board.lastLinesRemoved() == 1)
    {
      my_total_score += GRID;
    }
    
    my_score.setText("SCORE| " + my_total_score);
    
    my_lvl.setText("LVL " + my_lines_cleared / GRID);
    
  }
  
}
