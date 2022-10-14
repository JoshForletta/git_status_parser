#![feature(str_split_as_str)]

use std::{
    default::Default,
    error::Error,
    fmt::{self, Debug, Display},
    path::PathBuf,
    str::{FromStr, Split},
};

#[derive(Clone)]
pub struct ParsingError(String);

impl Error for ParsingError {}

impl Debug for ParsingError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self, self.0)
    }
}

impl Display for ParsingError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Error parsing git status")
    }
}

#[derive(Debug, PartialEq)]
pub enum EntryStatus {
    Unmodified,
    Modified,
    FileTypeChanged,
    Added,
    Deleted,
    Renamed,
    Copied,
    UpdatedUnmerged,
}

impl Default for EntryStatus {
    fn default() -> Self {
        Self::Unmodified
    }
}

impl EntryStatus {
    pub fn from_char(c: &char) -> Result<EntryStatus, &'static str> {
        Ok(match c {
            '.' | ' ' => Self::Unmodified,
            'M' => Self::Modified,
            'T' => Self::FileTypeChanged,
            'A' => Self::Added,
            'D' => Self::Deleted,
            'R' => Self::Renamed,
            'C' => Self::Copied,
            'U' => Self::UpdatedUnmerged,
            _ => return Err("Invalid status character"),
        })
    }
}

#[derive(Debug, Default, PartialEq)]
pub struct SubmoduleState {
    pub commit: bool,
    pub tracked: bool,
    pub untracked: bool,
}

#[derive(Debug, PartialEq)]
pub struct AheadBehind {
    pub ahead: i32,
    pub behind: i32,
}

#[derive(Debug, Default, PartialEq)]
pub struct Entry {
    pub index: EntryStatus,
    pub working_tree: EntryStatus,
    pub submodule: Option<SubmoduleState>,
    pub file_mode_head: i32,
    pub file_mode_index: i32,
    pub file_mode_working_tree: i32,
    pub object_head: String,
    pub object_index: String,
    pub rc_score: String,
    pub path: PathBuf,
    pub original_path: Option<PathBuf>,
}

#[derive(Debug, Default)]
pub struct UnmergedEntry {
    pub index: EntryStatus,
    pub working_tree: EntryStatus,
    pub submodule: Option<SubmoduleState>,
    pub file_mode_1: i32,
    pub file_mode_2: i32,
    pub file_mode_3: i32,
    pub file_mode_working_tree: i32,
    pub object_1: String,
    pub object_2: String,
    pub object_3: String,
    pub path: PathBuf,
}

#[derive(Debug, Default)]
pub struct GitStatus<'a> {
    pub branch_oid: Option<&'a str>,
    pub branch_head: Option<&'a str>,
    pub branch_upstream: Option<&'a str>,
    pub branch_ab: Option<AheadBehind>,
    pub entries: Vec<Entry>,
    pub unmerged: Vec<UnmergedEntry>,
    pub untracked: Vec<PathBuf>,
    pub ignored: Vec<PathBuf>,
}

impl<'a> GitStatus<'a> {
    pub fn parse(stream: &'a str) -> Result<GitStatus<'a>, ParsingError> {
        let mut gs: GitStatus = Default::default();

        for line in stream.split("\n") {
            let mut line = line.split(" ");
            match line.next() {
                Some("#") => parse_header(&mut line, &mut gs)?,
                Some("1") => parse_ordinary_entry(&mut line, &mut gs)?,
                Some("2") => parse_rename_copy_entry(&mut line, &mut gs)?,
                Some("?") => gs.untracked.push(match line.next() {
                    Some(s) => PathBuf::from_str(s).expect("`PathBuf::from_str` is infailable"),
                    None => return Err(ParsingError(String::from("Missing path token"))),
                }),
                Some("!") => gs.ignored.push(match line.next() {
                    Some(s) => PathBuf::from_str(s).expect("`PathBuf::from_str` is infailable"),
                    None => return Err(ParsingError(String::from("Missing path token"))),
                }),
                Some("u") => parse_unmerged_entry(&mut line, &mut gs)?,
                Some(s) if s.is_empty() => continue,
                Some(t) => return Err(ParsingError(format!("Invalid token {t}"))),
                None => return Err(ParsingError(String::from("Missing token")))
            };
        }

        Ok(gs)
    }
}

fn parse_header<'a>(
    split: &mut Split<'a, &'a str>,
    gs: &mut GitStatus<'a>,
) -> Result<(), ParsingError> {
    if let Some(token) = split.next() {
        match token {
            "branch.oid" => {
                gs.branch_oid = match split.next() {
                    Some("(initial)") => None,
                    Some(commit) => Some(commit),
                    None => return Err(ParsingError(String::from("Missing commit token"))),
                }
            }
            "branch.head" => {
                gs.branch_head = match split.next() {
                    Some("(detached)") => None,
                    Some(commit) => Some(commit),
                    None => return Err(ParsingError(String::from("Missing head token"))),
                }
            }
            "branch.upstream" => {
                gs.branch_upstream = match split.next() {
                    Some(branch) => Some(branch),
                    None => {
                        return Err(ParsingError(String::from("Missing upstream branch token")))
                    }
                }
            }
            "branch.ab" => {
                gs.branch_ab = match (split.next(), split.next()) {
                    (Some(a), Some(b)) => match (a.parse::<i32>(), b.parse::<i32>()) {
                        (Ok(ahead), Ok(behind)) => Some(AheadBehind { ahead, behind }),
                        _ => {
                            return Err(ParsingError(String::from(
                                "Failed to parse ahead behind tokens into i32",
                            )))
                        }
                    },
                    _ => return Err(ParsingError(String::from("Invalid ahead behind token"))),
                }
            }
            _ => return Err(ParsingError(format!("Invalid header token: '{token}'"))),
        }
    }

    Ok(())
}

fn parse_ordinary_entry<'a>(
    split: &mut Split<'a, &'a str>,
    gs: &mut GitStatus<'a>,
) -> Result<(), ParsingError> {
    let (index, working_tree) = parse_section_status(split)?;

    gs.entries.push(Entry {
        index,
        working_tree,
        submodule: parse_submodule(split)?,
        file_mode_head: parse_file_mode(split)?,
        file_mode_index: parse_file_mode(split)?,
        file_mode_working_tree: parse_file_mode(split)?,
        object_head: parse_object_name(split)?,
        object_index: parse_object_name(split)?,
        path: parse_path(split)?,
        ..Default::default()
    });

    Ok(())
}

fn parse_rename_copy_entry<'a>(
    split: &mut Split<'a, &'a str>,
    gs: &mut GitStatus<'a>,
) -> Result<(), ParsingError> {
    let (index, working_tree) = parse_section_status(split)?;
    let submodule = parse_submodule(split)?;
    let file_mode_head = parse_file_mode(split)?;
    let file_mode_index = parse_file_mode(split)?;
    let file_mode_working_tree = parse_file_mode(split)?;
    let object_head = parse_object_name(split)?;
    let object_index = parse_object_name(split)?;
    let rc_score = match split.next() {
        Some(s) => String::from(s),
        None => return Err(ParsingError(String::from("Missing rc score token"))),
    };
    let (path, original_path) = parse_rename_copy_paths(split)?;

    gs.entries.push(Entry {
        index,
        working_tree,
        submodule,
        file_mode_head,
        file_mode_index,
        file_mode_working_tree,
        object_head,
        object_index,
        rc_score,
        path,
        original_path,
    });

    Ok(())
}

fn parse_unmerged_entry<'a>(
    split: &mut Split<'a, &'a str>,
    gs: &mut GitStatus<'a>,
) -> Result<(), ParsingError> {
    let (index, working_tree) = parse_section_status(split)?;

    gs.unmerged.push(UnmergedEntry {
        index,
        working_tree,
        submodule: parse_submodule(split)?,
        file_mode_1: parse_file_mode(split)?,
        file_mode_2: parse_file_mode(split)?,
        file_mode_3: parse_file_mode(split)?,
        file_mode_working_tree: parse_file_mode(split)?,
        object_1: parse_object_name(split)?,
        object_2: parse_object_name(split)?,
        object_3: parse_object_name(split)?,
        path: parse_path(split)?,
    });

    Ok(())
}

fn parse_section_status<'a>(
    split: &mut Split<'a, &'a str>,
) -> Result<(EntryStatus, EntryStatus), ParsingError> {
    match split.next() {
        Some(s) if s.len() == 2 => {
            let mut s = s.chars();
            match (
                EntryStatus::from_char(&s.next().expect("Length should be 2")),
                EntryStatus::from_char(&s.next().expect("Length should be 2")),
            ) {
                (Ok(index), Ok(working_tree)) => Ok((index, working_tree)),
                _ => {
                    return Err(ParsingError(String::from(
                        "Invalid entry section status token",
                    )))
                }
            }
        }
        _ => return Err(ParsingError(String::from("Invalid "))),
    }
}

fn parse_submodule(split: &mut Split<&str>) -> Result<Option<SubmoduleState>, ParsingError> {
    let s = match split.next() {
        Some(s) => s,
        None => return Err(ParsingError(String::from("Missing submodule state token"))),
    };

    let e = Err(ParsingError(String::from(format!(
        "Invalid submodule state token: '{s}'"
    ))));

    let mut s = s.chars();

    let mut state = match s.next() {
        Some('N') => return Ok(None),
        Some('S') => SubmoduleState::default(),
        _ => return e,
    };

    match s.next() {
        Some('C') => state.commit = true,
        Some('.') => (),
        _ => return e,
    };

    match s.next() {
        Some('M') => state.tracked = true,
        Some('.') => (),
        _ => return e,
    };

    match s.next() {
        Some('U') => state.untracked = true,
        Some('.') => (),
        _ => return e,
    }

    Ok(Some(state))
}

fn parse_file_mode(split: &mut Split<&str>) -> Result<i32, ParsingError> {
    match split.next() {
        Some(s) => match i32::from_str_radix(s, 8) {
            Ok(i) => Ok(i),
            Err(_) => Err(ParsingError(String::from(format!(
                "Invalid octal file mode: {:?}",
                s
            )))),
        },
        None => Err(ParsingError(String::from("Missing octal file mode token"))),
    }
}

fn parse_object_name(split: &mut Split<&str>) -> Result<String, ParsingError> {
    match split.next() {
        Some(s) => Ok(String::from(s)),
        None => return Err(ParsingError(String::from("Missing object name token"))),
    }
}

fn parse_path(split: &mut Split<&str>) -> Result<PathBuf, ParsingError> {
    let path = split.as_str();
    if path.is_empty() {
        return Err(ParsingError(String::from("Missing path token")));
    }

    Ok(PathBuf::from_str(path).expect("`PathBuf::from_str` is infailable"))
}

fn parse_rename_copy_paths(
    split: &mut Split<&str>,
) -> Result<(PathBuf, Option<PathBuf>), ParsingError> {
    let mut paths = split.as_str().split('\t');

    let path = match paths.next() {
        Some(s) => PathBuf::from_str(s).expect("`PathBuf::from_str` is infailable"),
        None => return Err(ParsingError(String::from("Missing path token"))),
    };

    let original_path = match paths.next() {
        Some(s) => Some(PathBuf::from_str(s).expect("`PathBuf::from_str` is infailable")),
        None => return Err(ParsingError(String::from("Missing original path token"))),
    };

    Ok((path, original_path))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse() {
        let stream = "# branch.oid 69311461eb463ecc58d3e5a992ad9ab36cdf33b7
# branch.head main
# branch.upstream origin/main
# branch.ab +0 -0
1 M. N... 100644 100644 100644 e69de29bb2d1d6434b8b29ae775ad8c2e48c5391 c7c7da3c64e86c3270f2639a1379e67e14891b6a test1.txt
1 .M N... 100644 100644 100644 e69de29bb2d1d6434b8b29ae775ad8c2e48c5391 e69de29bb2d1d6434b8b29ae775ad8c2e48c5391 test2.txt
2 R. N... 100644 100644 100644 e69de29bb2d1d6434b8b29ae775ad8c2e48c5391 e69de29bb2d1d6434b8b29ae775ad8c2e48c5391 R100 test3.txt	test 3.txt
? test4.txt";
        let gs = GitStatus::parse(&stream)
            .expect("`GitStatus::parse` didn't return `Some(GitStatus)` with given input");

        let entries = vec![
            Entry {
                index: EntryStatus::Modified,
                working_tree: EntryStatus::Unmodified,
                submodule: None,
                file_mode_head: 33188,
                file_mode_index: 33188,
                file_mode_working_tree: 33188,
                object_head: String::from("e69de29bb2d1d6434b8b29ae775ad8c2e48c5391"),
                object_index: String::from("c7c7da3c64e86c3270f2639a1379e67e14891b6a"),
                path: PathBuf::from_str("test1.txt").unwrap(),
                ..Default::default()
            },
            Entry {
                index: EntryStatus::Unmodified,
                working_tree: EntryStatus::Modified,
                submodule: None,
                file_mode_head: 33188,
                file_mode_index: 33188,
                file_mode_working_tree: 33188,
                object_head: String::from("e69de29bb2d1d6434b8b29ae775ad8c2e48c5391"),
                object_index: String::from("e69de29bb2d1d6434b8b29ae775ad8c2e48c5391"),
                path: PathBuf::from_str("test2.txt").unwrap(),
                ..Default::default()
            },
            Entry {
                index: EntryStatus::Renamed,
                working_tree: EntryStatus::Unmodified,
                submodule: None,
                file_mode_head: 33188,
                file_mode_index: 33188,
                file_mode_working_tree: 33188,
                object_head: String::from("e69de29bb2d1d6434b8b29ae775ad8c2e48c5391"),
                object_index: String::from("e69de29bb2d1d6434b8b29ae775ad8c2e48c5391"),
                path: PathBuf::from_str("test3.txt").unwrap(),
                rc_score: String::from("R100"),
                original_path: Some(PathBuf::from_str("test 3.txt").unwrap()),
            }
        ];

        assert_eq!(gs.branch_oid, Some("69311461eb463ecc58d3e5a992ad9ab36cdf33b7"));
        assert_eq!(gs.branch_head, Some("main"));
        assert_eq!(gs.branch_upstream, Some("origin/main"));
        assert_eq!(gs.untracked[0], PathBuf::from_str("test4.txt").unwrap());
        
        for (parsed, given) in gs.entries.iter().zip(entries) {
            assert_eq!(*parsed, given);
        };


        
    }

    #[test]
    fn parse_ignored_entry() {
        let stream = "! test4.txt";

        let mut gs = GitStatus::parse(&stream)
            .expect("`GitStatus::parse` didn't return `Some(GitStatus)` with given input");

        let entry = gs
            .ignored
            .pop()
            .expect("`GitStatus.entries` should have one element with given input");

        assert_eq!(entry, PathBuf::from_str("test4.txt").unwrap());
    }

    #[test]
    fn parse_untracked_entry() {
        let stream = "? test4.txt";

        let mut gs = GitStatus::parse(&stream)
            .expect("`GitStatus::parse` didn't return `Some(GitStatus)` with given input");

        let entry = gs
            .untracked
            .pop()
            .expect("`GitStatus.entries` should have one element with given input");

        assert_eq!(entry, PathBuf::from_str("test4.txt").unwrap());
    }

    #[test]
    fn parse_rename_copy_path() {
        let stream = "2 R. N... 100644 100644 100644 e69de29bb2d1d6434b8b29ae775ad8c2e48c5391 e69de29bb2d1d6434b8b29ae775ad8c2e48c5391 R100 test3.txt	test 3.txt";

        let gs = GitStatus::parse(&stream)
            .expect("`GitStatus::parse` didn't return `Some(GitStatus)` with given input");

        let entry = gs
            .entries
            .get(0)
            .expect("`GitStatus.entries` should have one element with given input");

        assert_eq!(
            entry.path,
            PathBuf::from_str("test3.txt").expect("`PathBuf::from_str` is infailable")
        );
        assert_eq!(
            entry.original_path,
            Some(PathBuf::from_str("test 3.txt").expect("`PathBuf::from_str` is infailable"))
        );
    }

    #[test]
    fn parse_path() {
        let stream = "1 M. N... 100644 100755 120000 e69de29bb2d1d6434b8b29ae775ad8c2e48c5391 c7c7da3c64e86c3270f2639a1379e67e14891b6a test1.txt";

        let gs = GitStatus::parse(&stream)
            .expect("`GitStatus::parse` didn't return `Some(GitStatus)` with given input");

        let entry = gs
            .entries
            .get(0)
            .expect("`GitStatus.entries` should have one element with given input");

        assert_eq!(
            entry.path,
            PathBuf::from_str("test1.txt").expect("`PathBuf::from_str` is infailable")
        );
    }

    #[test]
    fn parse_object_names() {
        let stream = "1 M. N... 100644 100755 120000 e69de29bb2d1d6434b8b29ae775ad8c2e48c5391 c7c7da3c64e86c3270f2639a1379e67e14891b6a test1.txt";

        let gs = GitStatus::parse(&stream)
            .expect("`GitStatus::parse` didn't return `Some(GitStatus)` with given input");

        let entry = gs
            .entries
            .get(0)
            .expect("`GitStatus.entries` should have one element with given input");

        assert_eq!(
            entry.object_head,
            "e69de29bb2d1d6434b8b29ae775ad8c2e48c5391"
        );
        assert_eq!(
            entry.object_index,
            "c7c7da3c64e86c3270f2639a1379e67e14891b6a"
        );
    }

    #[test]
    fn parse_file_mode() {
        let stream = "1 M. N... 100644 100755 120000 e69de29bb2d1d6434b8b29ae775ad8c2e48c5391 c7c7da3c64e86c3270f2639a1379e67e14891b6a test1.txt";

        let gs = GitStatus::parse(&stream)
            .expect("`GitStatus::parse` didn't return `Some(GitStatus)` with given input");

        let entry = gs
            .entries
            .get(0)
            .expect("`GitStatus.entries` should have one element with given input");

        assert_eq!(entry.file_mode_head, 33188);
        assert_eq!(entry.file_mode_index, 33261);
        assert_eq!(entry.file_mode_working_tree, 40960);
    }

    #[test]
    fn parse_section_status() {
        let stream = "1 M. N... 100644 100644 100644 e69de29bb2d1d6434b8b29ae775ad8c2e48c5391 c7c7da3c64e86c3270f2639a1379e67e14891b6a test1.txt";

        let gs = GitStatus::parse(&stream)
            .expect("`GitStatus::parse` didn't return `Some(GitStatus)` with given input");

        let entry = gs
            .entries
            .get(0)
            .expect("`GitStatus.entries` should have one element with given input");

        assert_eq!(entry.index, EntryStatus::Modified);
        assert_eq!(entry.working_tree, EntryStatus::Unmodified);
    }

    #[test]
    fn parse_none_submodule_state() {
        let stream = "1 M. N... 100644 100644 100644 e69de29bb2d1d6434b8b29ae775ad8c2e48c5391 c7c7da3c64e86c3270f2639a1379e67e14891b6a test1.txt";

        let gs = GitStatus::parse(&stream)
            .expect("`GitStatus::parse` didn't return `Some(GitStatus)` with given input");

        assert_eq!(
            gs.entries
                .get(0)
                .expect("`GitStatus.entries` should have one element with given input")
                .submodule,
            None
        );
    }

    #[test]
    fn parse_submodule_state() {
        let stream = "1 M. SCM. 100644 100644 100644 e69de29bb2d1d6434b8b29ae775ad8c2e48c5391 c7c7da3c64e86c3270f2639a1379e67e14891b6a test1.txt";

        let gs = GitStatus::parse(&stream)
            .expect("`GitStatus::parse` didn't return `Some(GitStatus)` with given input");

        let state = match &gs
            .entries
            .get(0)
            .expect("`GitStatus.entries` should have one element with given input")
            .submodule
        {
            Some(s) => s,
            _ => panic!("`Entry.submodule` should be `Some<SubmoduleState>` with given input"),
        };

        assert!(state.commit);
        assert!(state.tracked);
        assert!(!state.untracked);
    }

    #[test]
    fn initial_branch_oid_returns_none() {
        let stream = "# branch.oid (initial)";

        let gs = GitStatus::parse(&stream)
            .expect("`GitStatus::parse` didn't return `Some(GitStatus)` with given input");

        assert_eq!(gs.branch_oid, None);
    }

    #[test]
    fn branch_oid() {
        let stream = "# branch.oid 69311461eb463ecc58d3e5a992ad9ab36cdf33b7";

        let gs = GitStatus::parse(&stream)
            .expect("`GitStatus::parse` didn't return `Some(GitStatus)` with given input");

        assert_eq!(
            gs.branch_oid
                .expect("`branch_oid` should be type `Some<&str>` with given input"),
            "69311461eb463ecc58d3e5a992ad9ab36cdf33b7"
        );
    }

    #[test]
    fn detatched_head_returns_none() {
        let stream = "# branch.head (detached)";

        let gs = GitStatus::parse(&stream)
            .expect("`GitStatus::parse` didn't return `Some(GitStatus)` with given input");

        assert_eq!(gs.branch_head, None);
    }

    #[test]
    fn branch_head() {
        let stream = "# branch.head main";

        let gs = GitStatus::parse(&stream)
            .expect("`GitStatus::parse` didn't return `Some(GitStatus)` with given input");

        assert_eq!(
            gs.branch_head
                .expect("`branch_head` should be type `Some<&str>` with given input"),
            "main"
        )
    }

    #[test]
    fn branch_upstream() {
        let stream = "# branch.upstream origin/main";

        let gs = GitStatus::parse(&stream)
            .expect("`GitStatus::parse` didn't return `Some(GitStatus)` with given input");

        assert_eq!(
            gs.branch_upstream
                .expect("`branch_upstream` should be type `Some<&str>` with given input"),
            "origin/main",
        )
    }

    #[test]
    fn branch_ab() {
        let stream = "# branch.ab +4 -3";

        let gs = GitStatus::parse(&stream)
            .expect("`GitStatus::parse` didn't return `Some(GitStatus)` with given input");

        assert_eq!(
            gs.branch_ab
                .expect("`branch_ab` should be type `Some<AheadBehind>` with given input"),
            AheadBehind {
                ahead: 4,
                behind: -3
            }
        )
    }
}
