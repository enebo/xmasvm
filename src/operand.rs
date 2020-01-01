#[derive(Debug, Clone, PartialEq, Copy)]
pub enum Tag {
    Direct,
    Indirect,
    Literal,
}

#[derive(Debug, Clone)]
pub struct Operand {
    pub(crate) tag: Tag,
    pub(crate) value: i32,
}

impl ToString for Operand {
    fn to_string(&self) -> String {
        format!(
            "{}{}",
            match self.tag {
                Tag::Direct => 'd',
                Tag::Indirect => 'i',
                Tag::Literal => 'l',
            },
            self.value.to_string()
        )
    }
}
