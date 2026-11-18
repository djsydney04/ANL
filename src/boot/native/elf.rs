//! Bounded ELF structure only. Success does not admit an executable image.
#![forbid(unsafe_code)]

use std::{collections::BTreeMap, fmt, ops::Range};

pub const MAX_OBJECT_BYTES: usize = 67_108_864;
pub const MAX_IMAGE_BYTES: usize = 8_388_608;
pub const MAX_PROGRAM_HEADERS: u64 = 16;
pub const MAX_SECTIONS: u64 = 128;
pub const MAX_SYMBOLS: u64 = 100_000;
pub const MAX_RELOCATIONS: u64 = 100_000;
pub const IMAGE_BASE: u64 = 0x8020_0000;
pub const IMAGE_LIMIT: u64 = IMAGE_BASE + 1_048_576;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArtifactKind {
    Object,
    Image,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorClass {
    Resource,
    Infrastructure,
    Unsupported,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StructuralError {
    pub class: ErrorClass,
    pub reason: &'static str,
}
impl fmt::Display for StructuralError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.reason)
    }
}
impl std::error::Error for StructuralError {}
type Result<T> = std::result::Result<T, StructuralError>;
fn invalid(reason: &'static str) -> StructuralError {
    StructuralError {
        class: ErrorClass::Infrastructure,
        reason,
    }
}
fn unsupported(reason: &'static str) -> StructuralError {
    StructuralError {
        class: ErrorClass::Unsupported,
        reason,
    }
}
fn require(ok: bool, reason: &'static str) -> Result<()> {
    if ok { Ok(()) } else { Err(invalid(reason)) }
}
fn limit(n: u64, cap: u64, reason: &'static str) -> Result<()> {
    if n <= cap {
        Ok(())
    } else {
        Err(StructuralError {
            class: ErrorClass::Resource,
            reason,
        })
    }
}
fn end(start: u64, size: u64) -> Result<u64> {
    start
        .checked_add(size)
        .ok_or_else(|| invalid("ELF range overflows"))
}
fn range(bytes: &[u8], offset: u64, size: u64) -> Result<Range<usize>> {
    let stop = end(offset, size)?;
    require(stop <= bytes.len() as u64, "ELF range escapes input")?;
    Ok(
        usize::try_from(offset).map_err(|_| invalid("ELF offset exceeds host range"))?
            ..usize::try_from(stop).map_err(|_| invalid("ELF end exceeds host range"))?,
    )
}
fn slice(bytes: &[u8], offset: u64, size: u64) -> Result<&[u8]> {
    Ok(&bytes[range(bytes, offset, size)?])
}
fn u16_at(bytes: &[u8], offset: u64) -> Result<u16> {
    Ok(u16::from_le_bytes(
        slice(bytes, offset, 2)?
            .try_into()
            .map_err(|_| invalid("short u16"))?,
    ))
}
fn u32_at(bytes: &[u8], offset: u64) -> Result<u32> {
    Ok(u32::from_le_bytes(
        slice(bytes, offset, 4)?
            .try_into()
            .map_err(|_| invalid("short u32"))?,
    ))
}
fn u64_at(bytes: &[u8], offset: u64) -> Result<u64> {
    Ok(u64::from_le_bytes(
        slice(bytes, offset, 8)?
            .try_into()
            .map_err(|_| invalid("short u64"))?,
    ))
}
fn table(bytes: &[u8], offset: u64, count: u64, stride: u64) -> Result<Range<usize>> {
    range(
        bytes,
        offset,
        count
            .checked_mul(stride)
            .ok_or_else(|| invalid("ELF table overflows"))?,
    )
}
fn aligned(value: u64, alignment: u64) -> bool {
    alignment <= 1 || (alignment.is_power_of_two() && value.is_multiple_of(alignment))
}

#[derive(Clone, Debug)]
pub struct Section<'a> {
    pub name: &'a str,
    pub kind: u32,
    pub flags: u64,
    pub address: u64,
    pub offset: u64,
    pub size: u64,
    pub link: u32,
    pub info: u32,
    pub alignment: u64,
    pub entry_size: u64,
}
#[derive(Clone, Debug)]
pub struct ProgramHeader {
    pub kind: u32,
    pub flags: u32,
    pub offset: u64,
    pub address: u64,
    pub physical: u64,
    pub file_size: u64,
    pub memory_size: u64,
    pub alignment: u64,
}
#[derive(Clone, Debug)]
pub struct Symbol<'a> {
    pub name: &'a str,
    pub binding: u8,
    pub kind: u8,
    pub visibility: u8,
    pub section: u16,
    pub value: u64,
    pub size: u64,
}
#[derive(Clone, Debug)]
pub struct SymbolTable<'a> {
    pub section: usize,
    pub symbols: Vec<Symbol<'a>>,
}
#[derive(Clone, Debug)]
pub struct Relocation {
    pub section: usize,
    pub target_section: usize,
    pub symbol_table: usize,
    pub offset: u64,
    pub symbol: usize,
    pub kind: u32,
    pub addend: i64,
}

/// A parsed structure, not an admission capability. Fields retain exact aliases.
#[derive(Debug)]
pub struct ElfStructure<'a> {
    pub kind: ArtifactKind,
    pub bytes: &'a [u8],
    pub entry: u64,
    pub sections: Vec<Section<'a>>,
    pub program_headers: Vec<ProgramHeader>,
    pub symbol_tables: Vec<SymbolTable<'a>>,
    pub relocations: Vec<Relocation>,
}

fn section(bytes: &[u8], at: u64) -> Result<Section<'_>> {
    let b = slice(bytes, at, 64)?;
    Ok(Section {
        name: "",
        kind: u32_at(b, 4)?,
        flags: u64_at(b, 8)?,
        address: u64_at(b, 16)?,
        offset: u64_at(b, 24)?,
        size: u64_at(b, 32)?,
        link: u32_at(b, 40)?,
        info: u32_at(b, 44)?,
        alignment: u64_at(b, 48)?,
        entry_size: u64_at(b, 56)?,
    })
}
struct Strings<'a> {
    text: &'a str,
    scanned: BTreeMap<u32, u32>,
}
fn strings<'a>(bytes: &'a [u8], section: &Section<'_>) -> Result<Strings<'a>> {
    require(section.kind == 3, "string-table reference has wrong type")?;
    let data = slice(bytes, section.offset, section.size)?;
    require(
        data.first() == Some(&0) && data.last() == Some(&0),
        "string table lacks boundary NUL",
    )?;
    Ok(Strings {
        text: std::str::from_utf8(data).map_err(|_| invalid("ELF string table is not UTF-8"))?,
        scanned: BTreeMap::new(),
    })
}
impl<'a> Strings<'a> {
    fn get(&mut self, offset: u32) -> Result<&'a str> {
        let start = offset as usize;
        require(
            start < self.text.len() && self.text.is_char_boundary(start),
            "string offset escapes table or UTF-8 boundary",
        )?;
        if let Some((_, stop)) = self.scanned.range(..=offset).next_back()
            && offset <= *stop
        {
            return Ok(&self.text[start..*stop as usize]);
        }
        let next = self
            .scanned
            .range(offset..)
            .next()
            .map(|(start, stop)| (*start, *stop));
        let scan_end = next.map_or(self.text.len(), |(start, _)| start as usize);
        let stop = match self.text.as_bytes()[start..scan_end]
            .iter()
            .position(|b| *b == 0)
        {
            Some(delta) => offset + delta as u32,
            None => next
                .map(|(_, stop)| stop)
                .ok_or_else(|| invalid("unterminated ELF string"))?,
        };
        self.scanned.insert(offset, stop);
        Ok(&self.text[start..stop as usize])
    }
}

/// Checks raw structure and fixed layout policy only; no instruction or DWARF analysis.
pub fn read_structure(bytes: &[u8], kind: ArtifactKind) -> Result<ElfStructure<'_>> {
    let cap = match kind {
        ArtifactKind::Object => MAX_OBJECT_BYTES,
        ArtifactKind::Image => MAX_IMAGE_BYTES,
    };
    limit(
        bytes.len() as u64,
        cap as u64,
        "native artifact byte limit exceeded",
    )?;
    let header = slice(bytes, 0, 64)?;
    require(
        &header[..7] == b"\x7fELF\x02\x01\x01",
        "not current little-endian ELF64",
    )?;
    require(
        header[7..16].iter().all(|b| *b == 0),
        "unsupported ELF ABI identification",
    )?;
    let expected_type = match kind {
        ArtifactKind::Object => 1,
        ArtifactKind::Image => 2,
    };
    require(
        u16_at(header, 16)? == expected_type
            && u16_at(header, 18)? == 243
            && u32_at(header, 20)? == 1
            && u32_at(header, 48)? == 0,
        "ELF type, machine, version or flags violate profile",
    )?;
    require(
        u16_at(header, 52)? == 64 && u16_at(header, 58)? == 64,
        "wrong ELF header entry size",
    )?;
    let entry = u64_at(header, 24)?;
    let phoff = u64_at(header, 32)?;
    let shoff = u64_at(header, 40)?;
    let mut phnum = u16_at(header, 56)? as u64;
    let mut shnum = u16_at(header, 60)? as u64;
    let mut shnames = u16_at(header, 62)? as u64;
    require(
        shoff >= 64 && aligned(shoff, 8),
        "invalid section table offset",
    )?;
    let zero = section(bytes, shoff)?;
    require(
        u32_at(bytes, shoff)? == 0
            && zero.kind == 0
            && zero.flags == 0
            && zero.address == 0
            && zero.offset == 0
            && zero.alignment == 0
            && zero.entry_size == 0,
        "invalid section zero",
    )?;
    let extended = shnum == 0 || phnum == 0xffff || shnames == 0xffff;
    if shnum == 0 {
        shnum = zero.size;
        require(shnum > 0, "empty extended section count")?;
    } else {
        require(zero.size == 0, "unexpected section-zero size")?;
    }
    if phnum == 0xffff {
        phnum = u64::from(zero.info);
        require(phnum > 0, "empty extended program-header count")?;
    } else {
        require(zero.info == 0, "unexpected section-zero info")?;
    }
    if shnames == 0xffff {
        shnames = u64::from(zero.link);
    } else {
        require(zero.link == 0, "unexpected section-zero link")?;
    }
    limit(
        phnum,
        MAX_PROGRAM_HEADERS,
        "program-header count limit exceeded",
    )?;
    limit(shnum, MAX_SECTIONS, "section count limit exceeded")?;
    require(
        shnames > 0 && shnames < shnum,
        "invalid section-name table index",
    )?;
    let shrange = table(bytes, shoff, shnum, 64)?;
    require(
        (phnum == 0 && phoff == 0 && u16_at(header, 54)? == 0)
            || (phnum > 0 && phoff >= 64 && aligned(phoff, 8) && u16_at(header, 54)? == 56),
        "invalid program-header table",
    )?;
    let phrange = table(bytes, phoff, phnum, 56)?;
    require(
        match kind {
            ArtifactKind::Object => phnum == 0 && entry == 0,
            ArtifactKind::Image => phnum > 0 && entry == IMAGE_BASE,
        },
        "entry or program headers violate artifact kind",
    )?;
    if extended {
        return Err(unsupported(
            "coherent within-cap extended ELF numbering is not implemented",
        ));
    }
    let mut sections = (0..shnum)
        .map(|i| section(bytes, shoff + i * 64))
        .collect::<Result<Vec<_>>>()?;
    let mut names = strings(bytes, &sections[shnames as usize])?;
    let mut file_ranges = vec![(0, 64), (shrange.start as u64, shrange.end as u64)];
    if phnum > 0 {
        file_ranges.push((phrange.start as u64, phrange.end as u64));
    }
    let mut symbol_count = 0;
    let mut relocation_count = 0;
    for (index, s) in sections.iter_mut().enumerate().skip(1) {
        s.name = names.get(u32_at(bytes, shoff + index as u64 * 64)?)?;
        require(!s.name.is_empty(), "non-null section has empty name")?;
        require(
            s.alignment <= 1 || s.alignment.is_power_of_two(),
            "section alignment is not a power of two",
        )?;
        require(
            aligned(s.address, s.alignment),
            "section address is misaligned",
        )?;
        require(s.link < shnum as u32, "section link escapes table")?;
        end(s.address, s.size)?;
        if s.kind != 8 {
            range(bytes, s.offset, s.size)?;
            require(
                aligned(s.offset, s.alignment),
                "section file offset is misaligned",
            )?;
            if s.size > 0 {
                file_ranges.push((s.offset, end(s.offset, s.size)?));
            }
        } else {
            require(
                s.offset <= bytes.len() as u64,
                "NOBITS nominal offset escapes input",
            )?;
        }
        require(s.flags & !0xf7 == 0, "forbidden section flags")?;
        require(
            s.flags & 1 == 0 || s.kind == 8,
            "file-backed writable section is forbidden",
        )?;
        require(s.flags & 5 != 5, "writable executable section is forbidden")?;
        require(
            s.flags & 2 == 0 || matches!(s.kind, 1 | 8),
            "allocated metadata or runtime section is forbidden",
        )?;
        match s.kind {
            1 | 3 | 8 | 0x7000_0003 => {
                require(
                    s.entry_size == 0
                        || (s.kind == 1 && s.flags & 0x10 != 0 && s.entry_size <= s.size),
                    "unexpected section entry size",
                )?;
            }
            2 => {
                require(
                    s.entry_size == 24 && s.size.is_multiple_of(24),
                    "invalid symbol table stride",
                )?;
                symbol_count = end(symbol_count, s.size / 24)?;
                limit(
                    symbol_count,
                    MAX_SYMBOLS,
                    "aggregate symbol count limit exceeded",
                )?;
            }
            4 | 9 => {
                require(
                    kind == ArtifactKind::Object,
                    "final image retains relocations",
                )?;
                let stride = if s.kind == 4 { 24 } else { 16 };
                require(
                    s.entry_size == stride && s.size.is_multiple_of(stride),
                    "invalid relocation stride",
                )?;
                require(
                    s.info > 0 && u64::from(s.info) < shnum,
                    "relocation target escapes sections",
                )?;
                relocation_count = end(relocation_count, s.size / stride)?;
                limit(
                    relocation_count,
                    MAX_RELOCATIONS,
                    "aggregate relocation count limit exceeded",
                )?;
            }
            18 => {
                require(
                    s.entry_size == 4 && s.size.is_multiple_of(4),
                    "invalid extended symbol-index stride",
                )?;
            }
            6 | 11 | 14..=16 => return Err(invalid("dynamic/runtime section is forbidden")),
            _ => return Err(invalid("section type is outside the initial profile")),
        }
        if kind == ArtifactKind::Object {
            require(s.address == 0, "object section has linked address")?;
        }
    }
    file_ranges.sort_unstable();
    require(
        file_ranges.windows(2).all(|w| w[0].1 <= w[1].0),
        "ELF payload/header file ranges overlap",
    )?;
    for s in sections.iter().skip(1) {
        if s.flags & 0x80 != 0 {
            require(
                s.link > 0 && sections[s.link as usize].flags & 4 != 0,
                "LINK_ORDER does not identify code",
            )?;
        } else if !matches!(s.kind, 2 | 4 | 9 | 18) {
            require(s.link == 0, "unexpected section link")?;
        }
        if !matches!(s.kind, 2 | 4 | 9) {
            require(s.info == 0, "unexpected section info")?;
        }
        if s.kind == 3 {
            strings(bytes, s)?;
        }
        if matches!(s.kind, 4 | 9) {
            require(s.flags == 0x40, "unexpected relocation section flags")?;
        }
    }
    let mut extended_symbols = false;
    for s in sections.iter().filter(|s| s.kind == 18) {
        let target = &sections[s.link as usize];
        require(
            s.flags == 0 && target.kind == 2 && s.size / 4 == target.size / 24,
            "invalid extended symbol-index backing",
        )?;
        for i in 0..s.size / 4 {
            let index = u32_at(bytes, s.offset + i * 4)?;
            let marker = u16_at(bytes, target.offset + i * 24 + 6)?;
            require(
                if marker == 0xffff {
                    index > 0 && (index as usize) < sections.len()
                } else {
                    index == 0
                },
                "inconsistent extended symbol index",
            )?;
        }
        require(
            !extended_symbols,
            "duplicate extended symbol-index representation",
        )?;
        extended_symbols = true;
    }
    if extended_symbols {
        return Err(unsupported(
            "coherent extended symbol-index representation is not implemented",
        ));
    }
    let mut program_headers = Vec::new();
    for i in 0..phnum {
        let b = slice(bytes, phoff + i * 56, 56)?;
        let p = ProgramHeader {
            kind: u32_at(b, 0)?,
            flags: u32_at(b, 4)?,
            offset: u64_at(b, 8)?,
            address: u64_at(b, 16)?,
            physical: u64_at(b, 24)?,
            file_size: u64_at(b, 32)?,
            memory_size: u64_at(b, 40)?,
            alignment: u64_at(b, 48)?,
        };
        range(bytes, p.offset, p.file_size)?;
        require(
            p.file_size <= p.memory_size && p.address == p.physical,
            "invalid program extent/physical address",
        )?;
        end(p.address, p.memory_size)?;
        program_headers.push(p);
    }
    let symbol_tables = read_symbols(bytes, kind, &sections)?;
    let relocations = read_relocations(bytes, &sections, &symbol_tables)?;
    let parsed = ElfStructure {
        kind,
        bytes,
        entry,
        sections,
        program_headers,
        symbol_tables,
        relocations,
    };
    if kind == ArtifactKind::Image {
        image_layout(&parsed)?;
    }
    Ok(parsed)
}

fn read_symbols<'a>(
    bytes: &'a [u8],
    kind: ArtifactKind,
    sections: &[Section<'a>],
) -> Result<Vec<SymbolTable<'a>>> {
    let mut tables = Vec::new();
    let mut functions = Vec::new();
    let mut string_tables = BTreeMap::new();
    for (section_index, s) in sections.iter().enumerate().filter(|(_, s)| s.kind == 2) {
        require(
            s.flags == 0 && s.link > 0 && u64::from(s.info) <= s.size / 24,
            "invalid symbol-table header",
        )?;
        if let std::collections::btree_map::Entry::Vacant(entry) = string_tables.entry(s.link) {
            entry.insert(strings(bytes, &sections[s.link as usize])?);
        }
        let names = string_tables
            .get_mut(&s.link)
            .ok_or_else(|| invalid("missing retained string table"))?;
        require(
            s.size >= 24 && slice(bytes, s.offset, 24)?.iter().all(|b| *b == 0),
            "invalid null symbol",
        )?;
        let mut symbols = Vec::new();
        for i in 0..s.size / 24 {
            let b = slice(bytes, s.offset + i * 24, 24)?;
            let symbol = Symbol {
                name: names.get(u32_at(b, 0)?)?,
                binding: b[4] >> 4,
                kind: b[4] & 15,
                visibility: b[5],
                section: u16_at(b, 6)?,
                value: u64_at(b, 8)?,
                size: u64_at(b, 16)?,
            };
            require(
                symbol.binding <= 2 && symbol.kind <= 4 && symbol.visibility <= 3,
                "forbidden symbol binding/type/visibility",
            )?;
            require(
                (i < u64::from(s.info)) == (symbol.binding == 0),
                "symbol local/global partition is inconsistent",
            )?;
            if symbol.section == 0 {
                require(
                    symbol.value == 0 && symbol.size == 0,
                    "invalid undefined symbol",
                )?;
                require(
                    kind == ArtifactKind::Object || symbol.name.is_empty(),
                    "final image has a named undefined symbol",
                )?;
            } else if symbol.section == 0xfff1 {
                require(symbol.kind != 2, "absolute function symbol is forbidden")?;
                end(symbol.value, symbol.size)?;
            } else {
                require(
                    usize::from(symbol.section) < sections.len(),
                    "symbol section escapes table",
                )?;
                let target = &sections[usize::from(symbol.section)];
                require(
                    symbol.value >= target.address
                        && end(symbol.value, symbol.size)? <= end(target.address, target.size)?,
                    "symbol escapes its section",
                )?;
                if symbol.kind == 2 {
                    require(
                        target.flags & 4 != 0
                            && aligned(symbol.value, 4)
                            && symbol.size.is_multiple_of(4),
                        "invalid function extent",
                    )?;
                    if symbol.size > 0 {
                        functions.push((
                            symbol.section,
                            symbol.value,
                            end(symbol.value, symbol.size)?,
                        ));
                    }
                }
            }
            symbols.push(symbol);
        }
        tables.push(SymbolTable {
            section: section_index,
            symbols,
        });
    }
    require(!tables.is_empty(), "required symbol table is absent")?;
    functions.sort_unstable();
    require(
        functions
            .windows(2)
            .all(|w| w[0].0 != w[1].0 || w[0] == w[1] || w[0].2 <= w[1].1),
        "partial function overlap",
    )?;
    Ok(tables)
}

fn relocation_width(kind: u32, target: &Section<'_>) -> Result<u64> {
    if target.flags & 4 != 0 {
        return match kind {
            16 | 17 | 23..=25 => Ok(4),
            18 | 19 => Ok(8),
            _ => Err(invalid("forbidden text relocation family")),
        };
    }
    if target.name == ".stack_sizes" {
        return if kind == 2 {
            Ok(8)
        } else {
            Err(invalid("forbidden stack relocation family"))
        };
    }
    if target.name.starts_with(".debug_") {
        return match kind {
            1 | 35 | 39 | 56 | 57 => Ok(4),
            2 | 36 | 40 => Ok(8),
            34 | 38 | 55 => Ok(2),
            33 | 37 | 52..=54 | 60 | 61 => Ok(1),
            _ => Err(invalid("forbidden debug relocation family")),
        };
    }
    Err(invalid("relocation target section is not permitted"))
}
fn read_relocations(
    bytes: &[u8],
    sections: &[Section<'_>],
    tables: &[SymbolTable<'_>],
) -> Result<Vec<Relocation>> {
    let mut rows = Vec::new();
    let mut implicit_addends = false;
    for (index, s) in sections
        .iter()
        .enumerate()
        .filter(|(_, s)| matches!(s.kind, 4 | 9))
    {
        let symbols = tables
            .iter()
            .find(|table| table.section == s.link as usize)
            .ok_or_else(|| invalid("relocation link does not identify a symbol table"))?;
        let target = &sections[s.info as usize];
        require(target.kind == 1, "relocation target is not PROGBITS")?;
        let stride = if s.kind == 4 { 24 } else { 16 };
        for i in 0..s.size / stride {
            let b = slice(bytes, s.offset + i * stride, stride)?;
            let info = u64_at(b, 8)?;
            let symbol = (info >> 32) as usize;
            require(
                symbol < symbols.symbols.len(),
                "relocation symbol escapes table",
            )?;
            let r = Relocation {
                section: index,
                target_section: s.info as usize,
                symbol_table: s.link as usize,
                offset: u64_at(b, 0)?,
                symbol,
                kind: info as u32,
                addend: if s.kind == 4 {
                    i64::from_le_bytes(
                        b[16..24]
                            .try_into()
                            .map_err(|_| invalid("short relocation addend"))?,
                    )
                } else {
                    0
                },
            };
            let width = relocation_width(r.kind, target)?;
            require(
                end(r.offset, width)? <= target.size,
                "relocation site escapes target",
            )?;
            if target.flags & 4 != 0 {
                require(aligned(r.offset, 4), "text relocation site is misaligned")?;
            }
            if s.kind == 4 {
                rows.push(r);
            }
        }
        implicit_addends |= s.kind == 9;
    }
    if implicit_addends {
        return Err(unsupported(
            "coherent implicit-addend relocations are not implemented",
        ));
    }
    Ok(rows)
}

fn unique_section<'a, 'b>(elf: &'b ElfStructure<'a>, name: &str) -> Result<&'b Section<'a>> {
    let mut found = elf.sections.iter().filter(|s| s.name == name);
    let first = found
        .next()
        .ok_or_else(|| invalid("required image section is absent"))?;
    require(
        found.next().is_none(),
        "required image section is duplicated",
    )?;
    Ok(first)
}
fn boundary(elf: &ElfStructure<'_>, name: &str, expected: u64) -> Result<()> {
    let symbols: Vec<_> = elf
        .symbol_tables
        .iter()
        .flat_map(|t| &t.symbols)
        .filter(|s| s.name == name)
        .collect();
    require(
        symbols.len() == 1 && symbols[0].section != 0 && symbols[0].value == expected,
        "image boundary symbol is missing or contradictory",
    )
}
fn image_layout(elf: &ElfStructure<'_>) -> Result<()> {
    let boot = unique_section(elf, ".boot_stack")?;
    let terminal = unique_section(elf, ".terminal_stack")?;
    require(
        boot.kind == 8
            && terminal.kind == 8
            && boot.size == 16_384
            && terminal.size == 4096
            && boot.flags & !3 == 0
            && terminal.flags & !3 == 0
            && boot.flags & 2 != 0
            && terminal.flags & 2 != 0
            && aligned(boot.address, 4096)
            && terminal.address == end(boot.address, boot.size)?,
        "stack section layout violates profile",
    )?;
    let stack_end = end(terminal.address, terminal.size)?;
    let mut loads = Vec::new();
    let mut counts = [0; 3];
    let mut stack_headers = 0;
    let mut attribute_headers = 0;
    for p in &elf.program_headers {
        match p.kind {
            1 => {
                require(
                    p.memory_size > 0
                        && p.address >= IMAGE_BASE
                        && end(p.address, p.memory_size)? <= IMAGE_LIMIT
                        && p.alignment == 4096
                        && p.offset % 4096 == p.address % 4096,
                    "LOAD extent/alignment violates profile",
                )?;
                match p.flags {
                    5 => {
                        counts[0] += 1;
                        require(
                            p.address == IMAGE_BASE && p.file_size == p.memory_size,
                            "invalid RX LOAD",
                        )?;
                    }
                    4 => {
                        counts[1] += 1;
                        require(
                            aligned(p.address, 4096) && p.file_size == p.memory_size,
                            "invalid R LOAD",
                        )?;
                    }
                    6 => {
                        counts[2] += 1;
                        require(
                            p.address == boot.address
                                && p.file_size == 0
                                && end(p.address, p.memory_size)? == stack_end,
                            "invalid RW stack LOAD",
                        )?;
                    }
                    _ => return Err(invalid("forbidden LOAD permissions")),
                }
                loads.push(p);
            }
            0x6474_e551 => {
                stack_headers += 1;
                require(
                    p.flags == 6
                        && p.offset == 0
                        && p.address == 0
                        && p.file_size == 0
                        && p.memory_size == 0
                        && (p.alignment == 0 || p.alignment == 16),
                    "invalid GNU_STACK header",
                )?;
            }
            0x7000_0003 => {
                attribute_headers += 1;
                let a = unique_section(elf, ".riscv.attributes")?;
                require(
                    a.kind == 0x7000_0003
                        && a.flags == 0
                        && p.flags == 4
                        && p.address == 0
                        && p.offset == a.offset
                        && p.file_size == a.size
                        && p.memory_size == a.size
                        && p.alignment == 1,
                    "attribute program header disagrees with section",
                )?;
            }
            _ => return Err(invalid("forbidden program-header type")),
        }
    }
    require(
        counts[0] == 1
            && counts[1] <= 1
            && counts[2] == 1
            && stack_headers == 1
            && attribute_headers == 1,
        "missing or duplicated image segment role",
    )?;
    loads.sort_by_key(|p| p.address);
    require(
        loads
            .windows(2)
            .all(|w| w[0].address + w[0].memory_size <= w[1].address),
        "LOAD memory ranges overlap",
    )?;
    for s in elf.sections.iter().skip(1) {
        if s.flags & 2 == 0 {
            require(s.address == 0, "nonallocated section has image address")?;
            continue;
        }
        let expected = match s.name {
            ".text.entry" | ".text" => {
                require(
                    s.kind == 1
                        && s.flags == 6
                        && s.size > 0
                        && aligned(s.address, 4)
                        && s.size.is_multiple_of(4),
                    "invalid executable image section",
                )?;
                5
            }
            ".rodata" => {
                require(
                    s.kind == 1 && s.flags == 2 && s.size > 0,
                    "invalid rodata image section",
                )?;
                4
            }
            ".boot_stack" | ".terminal_stack" => 6,
            _ => return Err(invalid("unexpected allocated image section")),
        };
        let containers: Vec<_> = loads
            .iter()
            .filter(|p| {
                p.flags == expected
                    && s.address >= p.address
                    && end(s.address, s.size).is_ok_and(|stop| stop <= p.address + p.memory_size)
            })
            .collect();
        require(
            containers.len() == 1,
            "allocated section lacks unique matching LOAD",
        )?;
        let p = containers[0];
        if s.kind != 8 {
            require(
                s.offset == p.offset + (s.address - p.address)
                    && end(s.offset, s.size)? <= p.offset + p.file_size,
                "section file/address mapping disagrees with LOAD",
            )?;
        }
    }
    let text_entry = unique_section(elf, ".text.entry")?;
    unique_section(elf, ".text")?;
    require(
        text_entry.address == IMAGE_BASE,
        "entry section is not at image base",
    )?;
    boundary(elf, "anl_boot_entry", IMAGE_BASE)?;
    boundary(elf, "__anl_image_start", IMAGE_BASE)?;
    boundary(elf, "__anl_image_end", stack_end)?;
    boundary(elf, "__anl_boot_stack_start", boot.address)?;
    boundary(elf, "__anl_boot_stack_top", terminal.address)?;
    boundary(elf, "__anl_terminal_stack_start", terminal.address)?;
    boundary(elf, "__anl_terminal_stack_top", stack_end)?;
    Ok(())
}
