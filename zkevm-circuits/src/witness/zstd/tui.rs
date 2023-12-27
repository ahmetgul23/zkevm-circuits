use std::{error::Error, io};

use crossterm::{
    event::{self, DisableMouseCapture, EnableMouseCapture, Event, KeyCode, KeyEventKind},
    execute,
    terminal::{disable_raw_mode, enable_raw_mode, EnterAlternateScreen, LeaveAlternateScreen},
};
use eth_types::Field;
use ratatui::{prelude::*, widgets::*};

use super::ZstdWitnessRow;

struct App<F> {
    state: TableState,
    rows: Vec<ZstdWitnessRow<F>>,
}

impl<F: Field> App<F> {
    fn new(rows: &[ZstdWitnessRow<F>]) -> Self {
        Self {
            state: TableState::default(),
            rows: rows.to_vec(),
        }
    }

    fn next(&mut self) {
        let i = match self.state.selected() {
            Some(i) => {
                if i >= self.rows.len() - 1 {
                    0
                } else {
                    i + 1
                }
            }
            None => 0,
        };
        self.state.select(Some(i));
    }

    fn previous(&mut self) {
        let i = match self.state.selected() {
            Some(i) => {
                if i == 0 {
                    self.rows.len() - 1
                } else {
                    i - 1
                }
            }
            None => 0,
        };
        self.state.select(Some(i));
    }
}

fn run_app<B: Backend, F: Field>(terminal: &mut Terminal<B>, mut app: App<F>) -> io::Result<()> {
    loop {
        terminal.draw(|frame| ui(frame, &mut app))?;

        if let Event::Key(k) = event::read()? {
            if k.kind == KeyEventKind::Press {
                match k.code {
                    KeyCode::Char('q') => return Ok(()),
                    KeyCode::Down => app.next(),
                    KeyCode::Up => app.previous(),
                    _ => {}
                }
            }
        }
    }
}

fn ui<F: Field>(frame: &mut Frame, app: &mut App<F>) {
    let rects = Layout::default()
        .constraints([Constraint::Percentage(100)])
        .split(frame.size());
    let selected_style = Style::default().add_modifier(Modifier::REVERSED);
    let normal_style = Style::default().bg(Color::Blue);
    let header_cells = [
        "Byte IDX",
        "Value Byte",
        "Tag",
        "Tag Length",
        "Tag IDX",
        "Decoded Byte",
    ]
    .iter()
    .map(|&h| Cell::from(h).style(Style::default().fg(Color::Red)));
    let header = Row::new(header_cells)
        .style(normal_style)
        .height(1)
        .bottom_margin(1);
    let rows = app.rows.iter().map(|row| {
        Row::new([
            Cell::from(row.encoded_data.byte_idx.to_string()),
            Cell::from(row.encoded_data.value_byte.to_string()),
            Cell::from(row.state.tag.to_string()),
            Cell::from(row.state.tag_len.to_string()),
            Cell::from(row.state.tag_idx.to_string()),
            Cell::from(row.decoded_data.decoded_byte.to_string()),
        ])
        .height(2)
        .bottom_margin(1)
    });
    let widths = [
        Constraint::Percentage(17),
        Constraint::Percentage(17),
        Constraint::Percentage(17),
        Constraint::Percentage(17),
        Constraint::Percentage(16),
        Constraint::Percentage(16),
    ];
    let t = Table::new(rows, widths)
        .header(header)
        .block(
            Block::default()
                .borders(Borders::ALL)
                .title("Zstd Witness Rows"),
        )
        .highlight_style(selected_style)
        .highlight_symbol(">> ");

    frame.render_stateful_widget(t, rects[0], &mut app.state);
}

pub fn draw_rows<F: Field>(rows: &[ZstdWitnessRow<F>]) -> Result<(), Box<dyn Error>> {
    enable_raw_mode()?;
    let mut stdout = io::stdout();
    execute!(stdout, EnterAlternateScreen, EnableMouseCapture)?;
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;

    let app = App::new(rows);
    let res = run_app(&mut terminal, app);

    disable_raw_mode()?;
    execute!(
        terminal.backend_mut(),
        LeaveAlternateScreen,
        DisableMouseCapture
    )?;
    terminal.show_cursor()?;

    if let Err(err) = res {
        println!("{err:?}");
    }

    Ok(())
}
