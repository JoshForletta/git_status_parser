use std::{
    default::Default,
    error::Error,
    fmt::{self, Debug, Display},
    str::Split,
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
pub struct AheadBehind {
    pub ahead: i32,
    pub behind: i32,
}

#[derive(Default)]
pub struct GitStatus<'a> {
    pub branch_oid: Option<&'a str>,
    pub branch_head: Option<&'a str>,
    pub branch_upstream: Option<&'a str>,
    pub branch_ab: Option<AheadBehind>,
}

impl<'a> GitStatus<'a> {
    pub fn parse(stream: &'a str) -> Result<GitStatus<'a>, ParsingError> {
        let mut gs: GitStatus = Default::default();

        for line in stream.split("\n") {
            let mut line = line.split(" ");
            match line.next() {
                Some("#") => parse_header(&mut line, &mut gs)?,
                Some(_) => panic!(),
                _ => return Err(ParsingError(String::from(""))),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn initial_branch_oid_returns_none() {
        let stream = "# branch.oid (initial)";

        let gs = GitStatus::parse(&stream)
            .expect("`GitStatus::parse` didn't return `Some(GitStatus)` with valid input");

        assert_eq!(gs.branch_oid, None);
    }

    #[test]
    fn branch_oid() {
        let stream = "# branch.oid 69311461eb463ecc58d3e5a992ad9ab36cdf33b7";

        let gs = GitStatus::parse(&stream)
            .expect("`GitStatus::parse` didn't return `Some(GitStatus)` with valid input");

        assert_eq!(
            gs.branch_oid
                .expect("`branch_oid` should be type `Some<&str>` with valide input"),
            "69311461eb463ecc58d3e5a992ad9ab36cdf33b7"
        );
    }

    #[test]
    fn detatched_head_returns_none() {
        let stream = "# branch.head (detached)";

        let gs = GitStatus::parse(&stream)
            .expect("`GitStatus::parse` didn't return `Some(GitStatus)` with valid input");

        assert_eq!(gs.branch_head, None);
    }

    #[test]
    fn branch_head() {
        let stream = "# branch.head main";

        let gs = GitStatus::parse(&stream)
            .expect("`GitStatus::parse` didn't return `Some(GitStatus)` with valid input");

        assert_eq!(
            gs.branch_head
                .expect("`branch_head` should be type `Some<&str>` with valid input"),
            "main"
        )
    }

    #[test]
    fn branch_upstream() {
        let stream = "# branch.upstream origin/main";

        let gs = GitStatus::parse(&stream)
            .expect("`GitStatus::parse` didn't return `Some(GitStatus)` with valid input");

        assert_eq!(
            gs.branch_upstream
                .expect("`branch_upstream` should be type `Some<&str>` with valid input"),
            "origin/main",
        )
    }

    #[test]
    fn branch_ab() {
        let stream = "# branch.ab +4 -3";

        let gs = GitStatus::parse(&stream)
            .expect("`GitStatus::parse` didn't return `Some(GitStatus)` with valid input");

        assert_eq!(
            gs.branch_ab
                .expect("`branch_ab` should be type `Some<AheadBehind>` with valid input"),
            AheadBehind {
                ahead: 4,
                behind: -3
            }
        )
    }
}
