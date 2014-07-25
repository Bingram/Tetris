package tetris.gui;

import javax.swing.UIManager;
import javax.swing.UnsupportedLookAndFeelException;

/**
 * Kick-start class with main method.
 * Creates the game frame, which then creates and
 * manages it's components from there on.
 * 
 * @author Brian Ingram
 * @version FINAL
 *
 */
public final class MainGame
{
  /**
   * Private constructor.
   */
  private MainGame()
  {
    //does nothing
  }
  
  /**
   * Main program, starts a game frame, packs and sets visible.
   * @param the_args String...
   */
  public static void main(final String... the_args)
  {
    final GameFrame game = new GameFrame();

    try
    {
      // set cross-platform Java look and feel
      UIManager.setLookAndFeel(UIManager.getCrossPlatformLookAndFeelClassName());
    }
    catch (final UnsupportedLookAndFeelException e)
    {
      assert false;
    }
    catch (final ClassNotFoundException e)
    {
      assert false;
    }
    catch (final InstantiationException e)
    {
      assert false;
    }
    catch (final IllegalAccessException e)
    {
      assert false;
    }
    
    game.pack();
    game.setVisible(true);
  }
}
