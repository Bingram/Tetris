package tetris.gui;

import java.awt.Color;
import java.awt.Font;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.BorderLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.ComponentAdapter;
import java.awt.event.ComponentEvent;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;

import java.util.Observable;
import java.util.Observer;

import javax.swing.ImageIcon;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JButton;
import javax.swing.JToggleButton;
import javax.swing.Timer;


import tetris.Board;
import tetris.audio.SoundPlayer;

/**
 * Main program for tetris game.
 * Creates all elements for game, active board, 
 * next piece display, and other GUI elements.
 * 
 * Audio files obtained from freesounds.org
 * Theme from YouTube video of original Tetris theme
 * 
 * @author Brian Ingram
 * @version FINAL
 */
@SuppressWarnings("serial")
public final class GameFrame extends JFrame implements Observer
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
   * Constant int value for timer in milliseconds.
   */
  private static final int TIME = 1000;
  
  /**
   * String constant for multiple uses of theme song control.
   */
  private static final String THEME = "tetris/audio/theme.wav";
  
  /**
   * Timer for automatic piece movement down.
   */
  private final Timer my_timer;
  
  /**
   * The tetris board currently in play.
   */
  private Board my_board;
  
  /**
   * Panel that displays the game board.
   */
  private final BoardPanel my_board_panel;
  
  /**
   * Panel that displays the current score information.
   */
  private final ScorePanel my_score_panel;
  
  /**
   * Panel that displays the current next_piece.
   */
  private final NextPiecePanel my_next_piece;
  
  /**
   * Sound player for music and other sounds.
   */
  private final SoundPlayer my_sounds = new SoundPlayer();
  
  /**
   * String for switching controls from left hand to right hand.
   */
  private final String my_controls;
  
  /**
   * Private constructor.
   */
  public GameFrame()
  {
    super("Tetris Knock-Off 3.0");
    getContentPane().setSize(new Dimension(351, 396));
    setSize(new Dimension(354, 460));
    my_board = new Board(GRID_Y, GRID_X, System.currentTimeMillis());
    
    my_board_panel = new BoardPanel(my_board);
    my_score_panel = new ScorePanel(my_board);
    my_next_piece = new NextPiecePanel(my_board);
    
    my_timer = new Timer(TIME, new MoveListener());
    
    my_controls = setControls();
    
    setupFrame();
  }
  
  /**
   * Shows a dialogue box before each game
   * asking if the player is right or left handed.
   * After a selection it displays the corresponding controls
   * and sets the controls for this game to their choice.
   * 
   * @return string control style
   */
  private String setControls()
  {
    String choice = null;
    final Object[] options = {"Left", "Right"};
    final int n = JOptionPane.showOptionDialog(this,
                      "Are you Left handed or Right handed?",
                      "Controls choice",
                      JOptionPane.YES_NO_OPTION,
                      JOptionPane.QUESTION_MESSAGE,
                      null,     
                      options,  
                      options[0]);
    if (n == JOptionPane.YES_OPTION)
    {
      choice = "LEFT";
      final ImageIcon icon1 = new ImageIcon("src/Left_Controls.png");
      JOptionPane.showMessageDialog(null, "SPACE is quick drop.", "Left Handed Controls",
         JOptionPane.INFORMATION_MESSAGE,   icon1);
      
    }
    else if (n == JOptionPane.NO_OPTION)
    {
      choice = "RIGHT";
      final ImageIcon icon1 = new ImageIcon("src/Right_Controls.png");
      JOptionPane.showMessageDialog(null, "SPACE is quick drop.", "Right Handed Controls",
         JOptionPane.INFORMATION_MESSAGE,   icon1);
    }
    
    return choice;
  }

  /**
   * Sets up GUI component panels and adds them to game frame.
   * Also attaches component listener to frame, attempting to resize/scale 
   * inner components. 
   */
  public void setupFrame()
  {
    final JPanel sidebar = new JPanel();
    final JPanel upperpanel = new JPanel();
    final JPanel infopanel = new JPanel();
    final JPanel menupanel = new JPanel();
    final JButton newgame = new JButton("New Game");
    final JToggleButton debugmirror = new JToggleButton("Set Mirror Mode");

    my_sounds.loop(THEME);
    
    getContentPane().setLayout(new BorderLayout());
    getContentPane().add(my_board_panel, BorderLayout.CENTER);
    getContentPane().add(sidebar, BorderLayout.EAST);
    
    my_next_piece.setBackground(Color.WHITE);
    my_next_piece.setLayout(new FlowLayout(FlowLayout.CENTER, GRID_X / 2, GRID_X / 2));
    my_score_panel.setRequestFocusEnabled(false);
    
    setupUpperPanel(upperpanel, new JLabel("Next Piece"));
    setupMenu(menupanel, newgame);
    
    sidebar.setLayout(new BorderLayout(0, 0));
    sidebar.setLayout(new BorderLayout());
    sidebar.add(menupanel, BorderLayout.SOUTH);
    sidebar.add(upperpanel, BorderLayout.NORTH);
    sidebar.add(infopanel, BorderLayout.CENTER);
    
    debugmirror.setRequestFocusEnabled(false);
    debugmirror.setFocusable(false); 
    
    infopanel.setBackground(Color.WHITE);
    infopanel.setLayout(new BorderLayout(0, 0));
    infopanel.add(my_score_panel, BorderLayout.NORTH);
    infopanel.add(newgame, BorderLayout.SOUTH);
    
    my_board_panel.createKeys();
    my_board_panel.setKeys(my_controls);
    
    my_timer.start();
    
    /**
     * Controls size of inner board panel.
     */
    addComponentListener(new ComponentAdapter()
    {
      @Override
      public void componentResized(final ComponentEvent the_event) 
      {        
        my_board_panel.setSize(my_board_panel.getSize().height / 2, 
                                   my_board_panel.getSize().height);
      }
    });
    
    setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
    my_board_panel.requestFocusInWindow();
  }
  
  /**
   * Sets up the upper panel containing the next piece display.
   * @param the_upper panel with next piece
   * @param the_label label next to piece
   */
  private void setupUpperPanel(final JPanel the_upper, final JLabel the_label)
  {
    the_upper.setRequestFocusEnabled(false);
    the_upper.setFocusable(false);
    the_upper.setBackground(Color.WHITE);
    the_upper.setLayout(new FlowLayout(FlowLayout.CENTER, GRID_X / 2, GRID_X / 2));
    the_upper.add(my_next_piece);
    the_label.setFont(new Font("Arial Black", Font.PLAIN, 14));
    the_label.setRequestFocusEnabled(false);
    the_label.setFocusable(false);
    the_upper.add(the_label);
  }
  
  /**
   * Sets up menu portion of game display.
   * @param the_menu panel being setup
   * @param the_new_game button placed in panel
   */
  private void setupMenu(final JPanel the_menu, final JButton the_new_game)
  {
    final JButton quitgame = new JButton("Quit");
    final JToggleButton pausegame = new JToggleButton("Pause");

    the_menu.setRequestFocusEnabled(false);
    the_menu.setFocusable(false);
    the_menu.add(pausegame);
    the_menu.add(quitgame);
    the_menu.setLayout(new FlowLayout(FlowLayout.CENTER, GRID_X / 2, GRID_X / 2));
    
    the_new_game.setRequestFocusEnabled(false);
    the_new_game.setFocusable(false);
    
    pausegame.setRequestFocusEnabled(false);
    pausegame.setFocusable(false);
    quitgame.setRequestFocusEnabled(false);
    quitgame.setFocusable(false);
    
    /**
     * Creates a new board, resets the other panels, resets timer
     * and pause/play button.
     */
    the_new_game.addActionListener(new ActionListener() 
    {
      @Override
      public void actionPerformed(final ActionEvent the_event)
      {        
        my_board = new Board(GRID_Y, GRID_X, System.currentTimeMillis());
        my_board_panel.newGame(my_board);
        my_score_panel.newGame(my_board);
        my_next_piece.newGame(my_board);
        pausegame.setEnabled(true);
        my_board_panel.setKeys(my_controls);
        my_timer.restart();
        my_sounds.play(THEME);
      }
    });
    
    /**
     * Stops the timer, clears action map keys, disables pause/play button.
     */
    quitgame.addActionListener(new ActionListener() 
    {
      @Override
      public void actionPerformed(final ActionEvent the_event)
      {
        my_timer.stop();
        my_sounds.stop(THEME);
        my_board_panel.getActionMap().clear();
        pausegame.setEnabled(false);
      }
    });    
    
    /**
     * Stops timer and changes text on first click.
     * Resets text and starts timer on second click.
     */
    pausegame.addItemListener(new ItemListener() 
    {
      @Override
      public void itemStateChanged(final ItemEvent the_event)
      {
        if (the_event.getStateChange() == ItemEvent.SELECTED)
        {
          my_sounds.pause(THEME);
          my_timer.stop();
          pausegame.setText("Play");
          my_board_panel.clearKeys();
        }
        else
        {
          my_timer.start();
          pausegame.setText("Pause");
          my_board_panel.setKeys(my_controls);
          my_sounds.play(THEME);
        } 
      }
    });
    
  }
  
  /**
   * Resets timer to original time minus passed int.
   * @param the_time int value of ms to remove
   */
  private void setTimer(final int the_time)
  {
    my_timer.setDelay(my_timer.getInitialDelay() - the_time);
  }
  
  @Override
  public void update(final Observable the_arg0, final Object the_arg1)
  {    
    if (my_score_panel.getLvl() % GRID_X == 0)
    {
      setTimer(my_score_panel.getLines());
    }
    
  }

  /**
   * Listener for timer.
   * Fires the moveDown on board.
   * @author Brian Ingram
   * @version FINAL
   */
  private class MoveListener implements ActionListener
  {
    /**
     * Adds the action to board as observer.
     * @param the_event timer fires
     */
    public void actionPerformed(final ActionEvent the_event)
    { 
      if (my_score_panel.getLvl() >= 1)
      {
        my_board_panel.setMirror(false);
      }
      else
      {
        my_board_panel.setMirror(true);
      }
      
      if (my_board.isFull())
      {
        my_sounds.stop(THEME);
        my_timer.stop();
        my_sounds.play("tetris/audio/beep.wav");
        repaint();
        my_board_panel.gameOver();
      }
      else
      {
        my_board.moveDown();
        repaint();
      }      
    }
  }
  
}
