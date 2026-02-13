"""Minesweeper game with full structure and docstrings, Pylint compliant."""

# === Standard library ===
import os
import json
import time
import random
from queue import Queue

# === Third-party ===
import pygame
from pygame.locals import (  # pylint: disable=import-error,no-name-in-module
    QUIT,
    KEYDOWN,
    K_ESCAPE,
    MOUSEBUTTONDOWN,
)

# ---- Constants ----
TILE_SIZE = 40
PLUS_HEIGHT = 40
HISTORY_FILE = "minesweeper_history.json"

# ---- Colors ----
WHITE = (255, 255, 255)
BLACK = (0, 0, 0)
GRAY = (200, 200, 200)


def init_pygame():
    """Initialize pygame and load all tile images.

    Returns:
        dict[str, Surface]: Map tile keys (" ", "flag", "mine", "empty", "1".."8")
        to scaled pygame surfaces.
    """
    pygame.init()  # pylint: disable=no-member
    images = {
        " ": pygame.image.load("tile_back.png"),
        "flag": pygame.image.load("tile_flag.png"),
        "mine": pygame.image.load("tile_mine.png"),
        "empty": pygame.image.load("tile_empty.png"),
    }
    for i in range(1, 9):
        images[str(i)] = pygame.image.load(f"tile_{i}.png")
    for key in images:
        images[key] = pygame.transform.scale(images[key], (TILE_SIZE, TILE_SIZE))
    return images


def window_width(cols):
    """Compute the window width in pixels.

    Args:
        cols: Number of columns in the field.

    Returns:
        Window width in pixels.
    """
    return cols * TILE_SIZE


def window_height(rows):
    """Compute the window height in pixels.

    Args:
        rows: Number of rows in the field.

    Returns:
        Window height in pixels (grid + header).
    """
    return rows * TILE_SIZE + PLUS_HEIGHT


def ui_font_size(rows: int, cols: int) -> int:
    """Compute responsive UI font size that fits inside the header.

    Args:
        rows: Number of rows in the field.
        cols: Number of columns in the field.

    Returns:
        Font size in pixels (bounded by the header height).
    """
    grid_w = window_width(cols)
    grid_h = rows * TILE_SIZE
    base = int(0.06 * min(grid_w, grid_h))
    return max(12, min(PLUS_HEIGHT - 6, base))


class GameState:  # pylint: disable=too-many-instance-attributes
    """Minesweeper game state.

    Attributes:
        rows (int): Number of rows in the board.
        cols (int): Number of columns in the board.
        num_mines (int): Total number of mines.
        values (list[list[int]]): -1 = mine, 0–8 = adjacent mines.
        opened (list[list[bool]]): Which cells have been revealed.
        flagged (list[list[bool]]): Which cells are flagged.
        flag_count (int): Remaining flags.
        turns (int): Player actions (reveal/flag).
        elapsed_time (int): Duration of play in seconds.
        game_over (bool): True if game has ended.
        result (str|None): "won", "lost", or None if ongoing.
    """

    MINE = -1

    def __init__(self, rows: int, cols: int, num_mines: int):
        self.rows = rows
        self.cols = cols
        self.num_mines = num_mines

        # Core structures (created together)
        self.values = [[0 for _ in range(cols)] for _ in range(rows)]
        self.opened = [[False for _ in range(cols)] for _ in range(rows)]
        self.flagged = [[False for _ in range(cols)] for _ in range(rows)]

        # Runtime state
        self.flag_count = num_mines
        self.turns = 0
        self.elapsed_time = 0
        self.start_time = time.time()
        self.game_over = False
        self.result = None  # "won" | "lost"

        self.safe_total = self.rows * self.cols - self.num_mines
        self.safe_opened = 0

        # Neighbors cache (must exist before placement)
        self._neighbor_cache: dict[tuple[int, int], list[tuple[int, int]]] = {}

        # Place mines & precompute numbers
        self._place_mines_and_numbers()

    # ---------- neighbors ----------
    def _get_neighbors(self, x: int, y: int) -> list[tuple[int, int]]:
        """Return cached 8-neighborhood around (x, y)."""
        if not hasattr(self, "_neighbor_cache"):
            self._neighbor_cache = {}
        key = (x, y)
        if key in self._neighbor_cache:
            return self._neighbor_cache[key]
        nbrs = [
            (nx, ny)
            for dx in (-1, 0, 1)
            for dy in (-1, 0, 1)
            if (dx or dy)
            and 0 <= (nx := x + dx) < self.cols
            and 0 <= (ny := y + dy) < self.rows
        ]
        self._neighbor_cache[key] = nbrs
        return nbrs

    def _neighbors(self, x: int, y: int) -> list[tuple[int, int]]:
        """Alias for compatibility."""
        return self._get_neighbors(x, y)

    # ---------- placement & numbers ----------
    def _place_mines_and_numbers(self) -> None:
        """Place exactly N mines and precompute adjacent numbers for all cells."""
        all_cells = [(x, y) for x in range(self.cols) for y in range(self.rows)]
        for (mx, my) in random.sample(all_cells, self.num_mines):
            self.values[my][mx] = self.MINE
        for y in range(self.rows):
            for x in range(self.cols):
                if self.values[y][x] == self.MINE:
                    for nx, ny in self._get_neighbors(x, y):
                        if self.values[ny][nx] != self.MINE:
                            self.values[ny][nx] += 1

    # ---------- gameplay ----------
    def _flood_open(self, x: int, y: int) -> None:
        """Open cells using BFS: expand only from zeros; direct mine click loses."""
        q = Queue()
        q.put((x, y))
        while not q.empty():
            cx, cy = q.get()

            if self.opened[cy][cx] or self.flagged[cy][cx]:
                continue

            if self.values[cy][cx] == self.MINE:
                self.opened[cy][cx] = True
                self.end_game(False)
                return

            self.opened[cy][cx] = True
            self.safe_opened += 1
            if self.safe_opened == self.safe_total:
                self.end_game(True)
                return

            if self.values[cy][cx] == 0:
                for nx, ny in self._get_neighbors(cx, cy):
                    if not self.opened[ny][nx] and not self.flagged[ny][nx]:
                        if self.values[ny][nx] != self.MINE:
                            q.put((nx, ny))

    def reveal_cell(self, x: int, y: int) -> bool:
        """Reveal a cell and propagate if zero. Return True if state changed."""
        if self.game_over or self.opened[y][x] or self.flagged[y][x]:
            return False
        self._flood_open(x, y)
        return True

    def flag_cell(self, x: int, y: int) -> bool:
        """Toggle a flag on a covered cell. Return True if state changed."""
        if self.game_over or self.opened[y][x]:
            return False
        if self.flagged[y][x]:
            self.flagged[y][x] = False
            self.flag_count += 1
            return True
        if self.flag_count > 0:
            self.flagged[y][x] = True
            self.flag_count -= 1
            return True
        return False

    def update_time(self) -> None:
        """Update elapsed in seconds if the game is not over."""
        if not self.game_over:
            self.elapsed_time = int(time.time() - self.start_time)

    def end_game(self, won: bool) -> None:
        """Finalize the game, persist statistics, and announce the outcome."""
        self.game_over = True
        self.elapsed_time = int(time.time() - self.start_time)
        self.result = "won" if won else "lost"

        save_statistics(self.result, self.elapsed_time, self.turns, self.flag_count)

        if won:
            print("Victory! Close the window or press ESC/click to return to menu.")
        else:
            print("Game Over: You hit a mine. Close the game window to exit.")

    # ---------- view helper ----------
    def tile_key_at(self, x: int, y: int) -> str:
        """Map the internal cell state to a tile image key."""
        if self.flagged[y][x] and not self.opened[y][x]:
            return "flag"
        if not self.opened[y][x]:
            return " "
        val = self.values[y][x]
        if val == self.MINE:
            return "mine"
        if val == 0:
            return "empty"
        return str(val)


def draw_ui(screen, font, state):
    """Render timer and flag count on the header."""
    state.update_time()
    timer_text = font.render(f"Time: {state.elapsed_time}s", True, BLACK)
    flag_text = font.render(f"Flags: {state.flag_count}", True, BLACK)
    screen.blit(timer_text, (screen.get_width() - timer_text.get_width() - 10, 10))
    screen.blit(flag_text, (10, 10))


def draw_grid(screen, state, images):
    """Render the grid using preloaded tile images."""
    for y in range(state.rows):
        for x in range(state.cols):
            key = state.tile_key_at(x, y)
            screen.blit(images[key], (x * TILE_SIZE, y * TILE_SIZE + PLUS_HEIGHT))


def save_statistics(result: str, elapsed_time: int, turns: int, mines_left: int) -> None:
    """Append a game stat entry to a JSON data file (machine-readable)."""
    entry = {
        "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
        "result": result,                         # "won" | "lost"
        # Write both keys for backwards compatibility
        "elapsed_time_seconds": elapsed_time,
        "elapsed_time": elapsed_time,
        "elapsed_time_minutes": round(elapsed_time / 60, 2),
        "turns": turns,
        "mines_left": mines_left,
    }

    stats: list = []
    if os.path.exists(HISTORY_FILE):
        try:
            with open(HISTORY_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
                if isinstance(data, list):
                    stats = data
        except (json.JSONDecodeError, OSError):
            # File error/incorrect format -> start new
            stats = []

    stats.append(entry)

    # Safe write (atomic-ish): write to temporary file and then replace
    tmp_path = HISTORY_FILE + ".tmp"
    with open(tmp_path, "w", encoding="utf-8") as f:
        json.dump(stats, f, indent=4)
    os.replace(tmp_path, HISTORY_FILE)




def load_statistics():
    """Load statistics from the JSON file; return [] if missing/invalid."""
    if not os.path.exists(HISTORY_FILE):
        return []
    try:
        with open(HISTORY_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
            return data if isinstance(data, list) else []
    except (json.JSONDecodeError, OSError):
        return []



def print_statistics():
    """Print game statistics in human-readable format (robust to old entries)."""
    stats = load_statistics()
    if not stats:
        print("No statistics available.")
        return

    print("\nGame Statistics:")
    for item in stats:
        # Skip non-dict entries (if there is old data in the wrong format)
        if not isinstance(item, dict):
            continue

        ts = item.get("timestamp", "?")
        res = str(item.get("result", "?")).capitalize()

        # Fallback: use elapsed_time_seconds if available, otherwise use old elapsed_time
        secs = item.get("elapsed_time_seconds", item.get("elapsed_time", 0))
        mins = item.get("elapsed_time_minutes", round(secs / 60, 2))

        turns = item.get("turns", "?")
        mines_left = item.get("mines_left", "?")

        print(
            f"{ts} - {res} - {secs}s "
            f"({mins}m) - Turns: {turns} - Mines left: {mines_left}"
        )



def max_grid_that_fits():
    """Compute the maximum (rows, cols) that fit the current desktop.

    Returns:
        A pair (max_rows, max_cols) that fits into the current display.
    """
    try:
        info = pygame.display.Info()
        desk_w, desk_h = info.current_w, info.current_h
    except pygame.error:  # pylint: disable=no-member
        desk_w, desk_h = 1280, 720

    max_cols = max(1, desk_w // TILE_SIZE)
    max_rows = max(1, (desk_h - PLUS_HEIGHT) // TILE_SIZE)
    return max_rows, max_cols


def prompt_value(name: str, min_value: int = 1, max_value: int | None = None) -> int:
    """Prompt a positive integer within the given bounds."""
    while True:
        raw = input(f"Enter number of {name}: ").strip()
        if not raw.isdigit():
            print("Invalid input: please enter a positive integer.")
            continue
        val = int(raw)
        if val < min_value:
            print(f"Invalid input: {name} must be at least {min_value}.")
            continue
        if max_value is not None and val > max_value:
            print(f"Invalid input: {name} must be at most {max_value}.")
            continue
        return val


def get_game_parameters():
    """Collect rows, columns, and mines from the player (each prompted once)."""
    max_rows, max_cols = max_grid_that_fits()
    print(f"(Your screen can fit up to {max_rows} rows × {max_cols} columns)")

    rows = prompt_value("rows", min_value=1, max_value=max_rows)
    cols = prompt_value("columns", min_value=1, max_value=max_cols)

    total_cells = rows * cols
    mines = prompt_value("mines", min_value=1, max_value=total_cells - 1)
    return rows, cols, mines


def handle_event(state, event, cols, rows):
    """Return 'quit' | 'back' | None depending on the action decided."""
    #1) always allow closing windows
    if event.type == QUIT:
        pygame.display.quit()
        return "quit"

    #2) if the game is over (win or lose):
    if state.game_over:
        # request: lose -> click to return to menu; let ESC work
        if event.type == MOUSEBUTTONDOWN or (event.type == KEYDOWN and event.key == K_ESCAPE):
            return "back"
        # other events ignored
        return None

    #3) playing: ESC to return to menu
    if event.type == KEYDOWN and event.key == K_ESCAPE:
        return "back"

    #4) handle mouse only; other events ignored
    if event.type != MOUSEBUTTONDOWN:
        return None

    #5) skip header area
    if event.pos[1] < PLUS_HEIGHT:
        return None

    gx = event.pos[0] // TILE_SIZE
    gy = (event.pos[1] - PLUS_HEIGHT) // TILE_SIZE
    if not (0 <= gx < cols and 0 <= gy < rows):
        return None

    if event.button == 1:
        if state.reveal_cell(gx, gy):
            state.turns += 1
    elif event.button == 3:
        if state.flag_cell(gx, gy):
            state.turns += 1
    return None



def main(rows: int, cols: int, num_mines: int) -> None:
    """Run the main game loop: events, drawing, and post-game behavior."""
    images = init_pygame()
    screen = pygame.display.set_mode((window_width(cols), window_height(rows)))
    pygame.display.set_caption("Minesweeper")
    clock = pygame.time.Clock()
    font = pygame.font.Font(None, ui_font_size(rows, cols))
    state = GameState(rows, cols, num_mines)

    while True:
        for event in pygame.event.get():
            action = handle_event(state, event, cols, rows)
            if action in ("quit", "back"):
                return

        screen.fill(GRAY)
        draw_grid(screen, state, images)
        draw_ui(screen, font, state)
        pygame.display.flip()
        clock.tick(60)



# ---- MENU ----
def _read_choice(prompt: str) -> str:
    """Read the first non-space character (case-insensitive) from input."""
    raw = input(prompt)
    for ch in raw.strip():
        return ch.lower()
    return ""


def show_menu() -> None:
    """Print the main menu (display only, no logic)."""
    print("==== Minesweeper Menu ====")
    print("[1/P] Play")
    print("[2/V] View Statistics")
    print("[3/Q] Quit")


def action_play() -> None | bool:
    """Start a new game and return to the menu afterwards."""
    rows, cols, mines = get_game_parameters()
    main(rows, cols, mines)
    return None


def action_view_stats() -> None | bool:
    """Print statistics and return to the menu."""
    print_statistics()
    return None


def action_quit() -> bool:
    """Announce exit and signal the menu loop to stop."""
    print("Goodbye!")
    return False


def menu() -> None:
    """Main menu loop: neat fork from choices to action functions."""
    actions = {
        "1": action_play,
        "p": action_play,
        "2": action_view_stats,
        "v": action_view_stats,
        "3": action_quit,
        "q": action_quit,
    }
    while True:
        show_menu()
        choice = _read_choice("Choose (1/2/3 or P/V/Q): ")
        func = actions.get(choice)
        if func is None:
            print("Invalid choice. Please try again.")
            continue
        if func() is False:
            break


if __name__ == "__main__":
    menu()
