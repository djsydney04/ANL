//! Exact executable text reconstruction only; no executable admission.
#![forbid(unsafe_code)]

pub mod elf;
use elf::{ArtifactKind, ElfStructure, ErrorClass, Relocation, StructuralError, Symbol};
use std::collections::{BTreeMap, BTreeSet};

pub const MAX_TEXT_BYTES: u64 = 1_048_576;
pub const MAX_WITNESS_ROWS: usize = 100_000;
pub const MAX_REPORT_BYTES: usize = 16_777_216;
type Result<T> = std::result::Result<T, StructuralError>;
fn error(class: ErrorClass, reason: &'static str) -> StructuralError {
    StructuralError { class, reason }
}
fn require(ok: bool, reason: &'static str) -> Result<()> {
    if ok {
        Ok(())
    } else {
        Err(error(ErrorClass::Infrastructure, reason))
    }
}
fn unsupported<T>(reason: &'static str) -> Result<T> {
    Err(error(ErrorClass::Unsupported, reason))
}
fn bounded(ok: bool, reason: &'static str) -> Result<()> {
    if ok {
        Ok(())
    } else {
        Err(error(ErrorClass::Resource, reason))
    }
}
fn end(a: u64, b: u64) -> Result<u64> {
    a.checked_add(b)
        .ok_or_else(|| error(ErrorClass::Infrastructure, "text range overflows"))
}
fn bytes(data: &[u8], start: u64, size: u64) -> Result<&[u8]> {
    let stop = end(start, size)?;
    require(stop <= data.len() as u64, "text range escapes bytes")?;
    let a = usize::try_from(start)
        .map_err(|_| error(ErrorClass::Infrastructure, "text index exceeds host"))?;
    let b = usize::try_from(stop)
        .map_err(|_| error(ErrorClass::Infrastructure, "text index exceeds host"))?;
    Ok(&data[a..b])
}
fn word(data: &[u8], at: u64) -> Result<u32> {
    Ok(u32::from_le_bytes(bytes(data, at, 4)?.try_into().map_err(
        |_| error(ErrorClass::Infrastructure, "short text word"),
    )?))
}
fn put(data: &mut [u8], at: u64, value: u32) -> Result<()> {
    let a = usize::try_from(at)
        .map_err(|_| error(ErrorClass::Infrastructure, "text index exceeds host"))?;
    let b = a
        .checked_add(4)
        .ok_or_else(|| error(ErrorClass::Infrastructure, "text index overflows"))?;
    require(b <= data.len(), "text patch escapes bytes")?;
    data[a..b].copy_from_slice(&value.to_le_bytes());
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SymbolId {
    pub object: u8,
    pub table: usize,
    pub index: usize,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct FunctionRange {
    pub section: u16,
    pub value: u64,
    pub size: u64,
}
#[derive(Clone, Debug)]
pub struct Alias<'a> {
    pub symbol: SymbolId,
    pub name: &'a str,
    pub binding: u8,
    pub visibility: u8,
}
#[derive(Clone, Debug)]
pub struct Patch {
    pub relocation_section: usize,
    pub offset: u64,
    pub kind: u32,
    pub symbol: SymbolId,
    pub addend: i64,
    pub target: u64,
    pub high_site: u64,
    pub high: i32,
    pub low: i16,
    pub original_words: Vec<u32>,
    pub linked_words: Vec<u32>,
}
#[derive(Clone, Debug)]
pub struct Contribution<'a> {
    pub object: u8,
    pub section: usize,
    pub image: FunctionRange,
    pub aliases: Vec<Alias<'a>>,
    pub image_aliases: Vec<Alias<'a>>,
    pub patches: Vec<Patch>,
}
/// Descriptive views only. Even a successful result has unchecked native obligations.
pub struct TextInspection<'a> {
    inputs: [&'a [u8]; 3],
    contributions: Vec<Contribution<'a>>,
    text_bytes: u64,
    rows: usize,
}
impl<'a> TextInspection<'a> {
    pub fn inputs(&self) -> [&'a [u8]; 3] {
        self.inputs
    }
    pub fn contributions(&self) -> &[Contribution<'a>] {
        &self.contributions
    }
    pub fn text_bytes(&self) -> u64 {
        self.text_bytes
    }
    pub fn witness_rows(&self) -> usize {
        self.rows
    }
}
struct Budget {
    rows: usize,
}
impl Budget {
    fn row(&mut self) -> Result<()> {
        bounded(
            self.rows < MAX_WITNESS_ROWS,
            "text witness row limit exceeded",
        )?;
        self.rows += 1;
        Ok(())
    }
}
struct Index<'s, 'a> {
    symbols: BTreeMap<SymbolId, &'s Symbol<'a>>,
    names: BTreeMap<&'a str, Vec<SymbolId>>,
    functions: BTreeMap<FunctionRange, Vec<SymbolId>>,
}
impl<'s, 'a> Index<'s, 'a> {
    fn new(elf: &'s ElfStructure<'a>, object: u8) -> Self {
        let mut this = Self {
            symbols: BTreeMap::new(),
            names: BTreeMap::new(),
            functions: BTreeMap::new(),
        };
        for table in &elf.symbol_tables {
            for (index, symbol) in table.symbols.iter().enumerate() {
                let id = SymbolId {
                    object,
                    table: table.section,
                    index,
                };
                this.symbols.insert(id, symbol);
                if !symbol.name.is_empty() {
                    this.names.entry(symbol.name).or_default().push(id);
                }
                if symbol.kind == 2
                    && symbol.size > 0
                    && symbol.section != 0
                    && symbol.section != 0xfff1
                {
                    this.functions
                        .entry(FunctionRange {
                            section: symbol.section,
                            value: symbol.value,
                            size: symbol.size,
                        })
                        .or_default()
                        .push(id);
                }
            }
        }
        this
    }
    fn symbol(&self, id: SymbolId) -> Result<&'s Symbol<'a>> {
        self.symbols
            .get(&id)
            .copied()
            .ok_or_else(|| error(ErrorClass::Infrastructure, "missing text symbol identity"))
    }
}
fn alias<'a>(id: SymbolId, s: &Symbol<'a>, budget: &mut Budget) -> Result<Alias<'a>> {
    if s.binding == 2 {
        return unsupported("weak function identity is not implemented");
    }
    budget.row()?;
    Ok(Alias {
        symbol: id,
        name: s.name,
        binding: s.binding,
        visibility: s.visibility,
    })
}
fn text_size(elf: &ElfStructure<'_>) -> Result<u64> {
    elf.sections
        .iter()
        .filter(|s| s.flags & 4 != 0)
        .try_fold(0, |sum, s| end(sum, s.size))
}
fn gap(data: &[u8]) -> Result<()> {
    if data.is_empty() {
        return Ok(());
    }
    if data.len().is_multiple_of(4)
        && data
            .as_chunks::<4>()
            .0
            .iter()
            .all(|w| w == &[0x13, 0, 0, 0])
    {
        unsupported("canonical text padding analysis is not implemented")
    } else {
        require(false, "unowned executable bytes")
    }
}
fn global_definitions(indices: &[Index<'_, '_>]) -> Result<()> {
    let mut defined = BTreeMap::new();
    for ix in indices {
        for (&id, &s) in &ix.symbols {
            if s.binding != 1 || s.section == 0 || s.name.is_empty() {
                continue;
            }
            let key = (id.object, s.section, s.value, s.size, s.kind, s.visibility);
            if let Some(old) = defined.insert(s.name, key) {
                require(old == key, "conflicting global strong definitions")?;
            }
        }
    }
    Ok(())
}
fn image_function(index: &Index<'_, '_>, name: &str) -> Result<FunctionRange> {
    let ids = index.names.get(name).ok_or_else(|| {
        error(
            ErrorClass::Infrastructure,
            "object function name is absent from image",
        )
    })?;
    let mut ranges = BTreeSet::new();
    let mut nonfunction = false;
    for id in ids {
        let s = index.symbol(*id)?;
        if s.kind != 2 || s.size == 0 {
            nonfunction = true;
            continue;
        }
        if s.binding == 2 {
            return unsupported("weak image function identity is not implemented");
        }
        ranges.insert(FunctionRange {
            section: s.section,
            value: s.value,
            size: s.size,
        });
    }
    require(
        !ranges.is_empty(),
        "object function name has no image function definition",
    )?;
    if nonfunction || ranges.len() != 1 {
        return unsupported("ambiguous image function name is not implemented");
    }
    ranges
        .first()
        .copied()
        .ok_or_else(|| error(ErrorClass::Infrastructure, "missing image function"))
}
fn contributions<'a>(
    objects: &[ElfStructure<'a>; 2],
    indices: &[Index<'_, 'a>; 2],
    image: &ElfStructure<'a>,
    final_ix: &Index<'_, 'a>,
    budget: &mut Budget,
) -> Result<Vec<Contribution<'a>>> {
    let mut result = Vec::new();
    let mut used = BTreeSet::new();
    let mut joins = BTreeMap::new();
    for (object, elf) in objects.iter().enumerate() {
        let ix = &indices[object];
        let mut by_section: BTreeMap<usize, Vec<FunctionRange>> = BTreeMap::new();
        for range in ix.functions.keys() {
            by_section
                .entry(usize::from(range.section))
                .or_default()
                .push(*range);
        }
        for (section, s) in elf
            .sections
            .iter()
            .enumerate()
            .filter(|(_, s)| s.flags & 4 != 0 && s.size > 0)
        {
            let fs = by_section
                .get(&section)
                .map(Vec::as_slice)
                .unwrap_or_default();
            if fs.len() > 1 {
                return unsupported("multiple functions in one text section are not implemented");
            }
            let Some(f) = fs.first() else {
                gap(bytes(elf.bytes, s.offset, s.size)?)?;
                return Err(error(
                    ErrorClass::Infrastructure,
                    "text section has no function",
                ));
            };
            let payload = bytes(elf.bytes, s.offset, s.size)?;
            gap(bytes(payload, 0, f.value)?)?;
            let stop = end(f.value, f.size)?;
            gap(bytes(payload, stop, s.size - stop)?)?;
            require(
                f.value == 0 && f.size == s.size,
                "text contribution is not one complete function",
            )?;
            let members = &ix.functions[f];
            let mut joined = None;
            let mut aliases = Vec::new();
            for id in members {
                let symbol = ix.symbol(*id)?;
                aliases.push(alias(*id, symbol, budget)?);
                if symbol.name.is_empty() {
                    continue;
                }
                let found = if let Some(found) = joins.get(symbol.name) {
                    *found
                } else {
                    let found = image_function(final_ix, symbol.name)?;
                    joins.insert(symbol.name, found);
                    found
                };
                require(
                    found.size == f.size,
                    "object and image function sizes disagree",
                )?;
                if let Some(old) = joined {
                    require(
                        old == found,
                        "object aliases join different image functions",
                    )?;
                } else {
                    joined = Some(found);
                }
            }
            let Some(joined) = joined else {
                return unsupported("unnamed function placement is not implemented");
            };
            require(
                used.insert(joined),
                "multiple objects join the same image contribution",
            )?;
            let mut final_aliases = Vec::new();
            let alias_keys: BTreeSet<_> = aliases
                .iter()
                .map(|a| (a.name, a.binding, a.visibility))
                .collect();
            let alias_names: BTreeSet<_> = aliases.iter().map(|a| a.name).collect();
            let mut final_keys = BTreeSet::new();
            let mut final_names = BTreeSet::new();
            for id in &final_ix.functions[&joined] {
                let symbol = final_ix.symbol(*id)?;
                let key = (symbol.name, symbol.binding, symbol.visibility);
                require(
                    alias_names.contains(symbol.name),
                    "image function alias lacks a matching object definition",
                )?;
                if !alias_keys.contains(&key) {
                    return unsupported(
                        "function alias binding or visibility transformation is not implemented",
                    );
                }
                final_keys.insert(key);
                final_names.insert(symbol.name);
                final_aliases.push(alias(*id, symbol, budget)?);
            }
            for a in &aliases {
                require(
                    final_names.contains(a.name),
                    "object function alias is absent from image",
                )?;
                if !final_keys.contains(&(a.name, a.binding, a.visibility)) {
                    return unsupported(
                        "function alias binding or visibility transformation is not implemented",
                    );
                }
            }
            budget.row()?;
            result.push(Contribution {
                object: object as u8,
                section,
                image: joined,
                aliases,
                image_aliases: final_aliases,
                patches: Vec::new(),
            });
        }
    }
    require(
        used.len() == final_ix.functions.len(),
        "image function has no object producer",
    )?;
    let mut per_section: BTreeMap<usize, Vec<FunctionRange>> = BTreeMap::new();
    for range in &used {
        per_section
            .entry(usize::from(range.section))
            .or_default()
            .push(*range);
    }
    for (index, section) in image
        .sections
        .iter()
        .enumerate()
        .filter(|(_, s)| s.flags & 4 != 0)
    {
        let payload = bytes(image.bytes, section.offset, section.size)?;
        let mut cursor = 0;
        for f in per_section
            .get(&index)
            .map(Vec::as_slice)
            .unwrap_or_default()
        {
            let at = f.value.checked_sub(section.address).ok_or_else(|| {
                error(ErrorClass::Infrastructure, "function precedes text section")
            })?;
            require(at >= cursor, "linked contributions overlap")?;
            gap(bytes(payload, cursor, at - cursor)?)?;
            cursor = end(at, f.size)?;
        }
        gap(bytes(payload, cursor, section.size - cursor)?)?;
    }
    Ok(result)
}

const BOUNDARIES: [&str; 6] = [
    "__anl_image_start",
    "__anl_image_end",
    "__anl_boot_stack_start",
    "__anl_boot_stack_top",
    "__anl_terminal_stack_start",
    "__anl_terminal_stack_top",
];
struct Resolver<'a, 'b> {
    objects: &'b [ElfStructure<'a>; 2],
    indices: &'b [Index<'b, 'a>; 2],
    image: &'b Index<'b, 'a>,
    placement: BTreeMap<(u8, usize), FunctionRange>,
    cache: BTreeMap<SymbolId, u64>,
    globals: BTreeMap<&'a str, (u64, u8, u8)>,
}
impl Resolver<'_, '_> {
    fn defined(&self, id: SymbolId, s: &Symbol<'_>) -> Result<u64> {
        if s.binding == 2 {
            return unsupported("weak relocation symbol is not implemented");
        }
        if s.section == 0xfff1 {
            return unsupported("object absolute-symbol placement is not implemented");
        }
        if let Some(range) = self.placement.get(&(id.object, usize::from(s.section))) {
            return end(range.value, s.value);
        }
        let section = &self.objects[usize::from(id.object)].sections[usize::from(s.section)];
        require(
            section.flags & 1 == 0 && section.flags & 0x400 == 0,
            "forbidden relocation data target",
        )?;
        unsupported("nontext object symbol placement is not implemented")
    }
    fn resolve(&mut self, id: SymbolId) -> Result<u64> {
        if let Some(value) = self.cache.get(&id) {
            return Ok(*value);
        }
        let value = self.resolve_uncached(id)?;
        self.cache.insert(id, value);
        Ok(value)
    }
    fn resolve_uncached(&mut self, id: SymbolId) -> Result<u64> {
        let s = self.indices[usize::from(id.object)].symbol(id)?;
        if s.binding == 2 {
            return unsupported("weak relocation symbol is not implemented");
        }
        if s.section != 0 {
            return self.defined(id, s);
        }
        require(
            s.binding == 1 && !s.name.is_empty(),
            "undefined relocation symbol is not global and named",
        )?;
        if let Some(&(value, kind, visibility)) = self.globals.get(s.name) {
            require(
                s.kind == 0 || s.kind == kind,
                "relocation symbol type changed",
            )?;
            require(
                s.visibility == visibility,
                "relocation symbol visibility changed",
            )?;
            return Ok(value);
        }
        let ids = self
            .image
            .names
            .get(s.name)
            .ok_or_else(|| error(ErrorClass::Infrastructure, "unresolved relocation symbol"))?;
        let mut final_symbol = None;
        for target in ids {
            let t = self.image.symbol(*target)?;
            require(
                t.section != 0 && t.binding == 1,
                "undefined symbol has incompatible image binding",
            )?;
            require(
                s.kind == 0 || s.kind == t.kind,
                "relocation symbol type changed",
            )?;
            require(
                s.visibility == t.visibility,
                "relocation symbol visibility changed",
            )?;
            let key = (t.section, t.value, t.size, t.kind);
            if let Some(old) = final_symbol {
                require(old == key, "ambiguous strong image symbol")?;
            } else {
                final_symbol = Some(key);
            }
        }
        let (_, value, _, kind) = final_symbol
            .ok_or_else(|| error(ErrorClass::Infrastructure, "empty image symbol resolution"))?;
        let mut definition = None;
        for ix in self.indices {
            for target in ix.names.get(s.name).map(Vec::as_slice).unwrap_or_default() {
                let t = ix.symbol(*target)?;
                if t.section == 0 || t.binding == 0 {
                    continue;
                }
                let actual = self.defined(*target, t)?;
                require(
                    actual == value,
                    "object definition and linked symbol disagree",
                )?;
                definition = Some(actual);
            }
        }
        if definition.is_some() || BOUNDARIES.contains(&s.name) {
            self.globals.insert(s.name, (value, kind, s.visibility));
            return Ok(value);
        }
        require(
            false,
            "external symbol lacks an object or linker-boundary definition",
        )?;
        Ok(value)
    }
}
fn halves(target: u64, place: u64) -> Result<(i32, i16)> {
    let delta = i128::from(target) - i128::from(place);
    let high = (delta + 2048).div_euclid(4096);
    let low = delta - high * 4096;
    require(
        (-524_288..=524_287).contains(&high)
            && (-2048..=2047).contains(&low)
            && high * 4096 + low == delta,
        "PC-relative relocation exceeds signed high/low range",
    )?;
    Ok((high as i32, low as i16))
}
fn target(base: u64, addend: i64) -> Result<u64> {
    let value = i128::from(base) + i128::from(addend);
    require(
        (i128::from(elf::IMAGE_BASE)..=i128::from(elf::IMAGE_LIMIT)).contains(&value),
        "relocation target escapes image domain",
    )?;
    u64::try_from(value).map_err(|_| {
        error(
            ErrorClass::Infrastructure,
            "relocation target exceeds address range",
        )
    })
}
fn legal_i_consumer(w: u32) -> bool {
    let op = w & 127;
    let f = w >> 12 & 7;
    match op {
        0x03 => f <= 6,
        0x67 => f == 0,
        0x13 => match f {
            0 | 2 | 3 | 4 | 6 | 7 => true,
            1 => w >> 26 == 0,
            5 => matches!(w >> 26, 0 | 16),
            _ => false,
        },
        0x1b => match f {
            0 => true,
            1 => w >> 25 == 0,
            5 => matches!(w >> 25, 0 | 32),
            _ => false,
        },
        _ => false,
    }
}
fn symbol_id(object: u8, r: &Relocation) -> SymbolId {
    SymbolId {
        object,
        table: r.symbol_table,
        index: r.symbol,
    }
}

/// Reparse exact held bytes and reconstruct text. No instruction or native admission.
pub fn inspect_text<'a>(
    entry: &'a [u8],
    program: &'a [u8],
    linked: &'a [u8],
) -> Result<TextInspection<'a>> {
    let objects = [
        elf::read_structure(entry, ArtifactKind::Object)?,
        elf::read_structure(program, ArtifactKind::Object)?,
    ];
    let image = elf::read_structure(linked, ArtifactKind::Image)?;
    let object_bytes = end(text_size(&objects[0])?, text_size(&objects[1])?)?;
    let image_bytes = text_size(&image)?;
    bounded(
        object_bytes <= MAX_TEXT_BYTES,
        "aggregate object text limit exceeded",
    )?;
    bounded(image_bytes <= MAX_TEXT_BYTES, "image text limit exceeded")?;
    let indices = [Index::new(&objects[0], 0), Index::new(&objects[1], 1)];
    let final_ix = Index::new(&image, 2);
    global_definitions(&indices)?;
    global_definitions(std::slice::from_ref(&final_ix))?;
    let mut budget = Budget { rows: 0 };
    let mut output = contributions(&objects, &indices, &image, &final_ix, &mut budget)?;
    let mut resolver = Resolver {
        objects: &objects,
        indices: &indices,
        image: &final_ix,
        placement: output
            .iter()
            .map(|c| ((c.object, c.section), c.image))
            .collect(),
        cache: BTreeMap::new(),
        globals: BTreeMap::new(),
    };
    let mut relocations: BTreeMap<(u8, usize), Vec<&Relocation>> = BTreeMap::new();
    let mut high_sites = BTreeMap::new();
    for (object, elf) in objects.iter().enumerate() {
        for r in &elf.relocations {
            if elf.sections[r.target_section].flags & 4 == 0 {
                continue;
            }
            relocations
                .entry((object as u8, r.target_section))
                .or_default()
                .push(r);
            if r.kind == 23 {
                require(
                    high_sites
                        .insert((object as u8, r.target_section, r.offset), r)
                        .is_none(),
                    "duplicate high relocation site",
                )?;
            }
        }
    }
    for c in &mut output {
        let elf = &objects[usize::from(c.object)];
        let s = &elf.sections[c.section];
        let original = bytes(elf.bytes, s.offset, s.size)?;
        let mut rebuilt = original.to_vec();
        let mut patches = relocations
            .remove(&(c.object, c.section))
            .unwrap_or_default();
        patches.sort_unstable_by_key(|r| (r.offset, r.kind));
        let mut previous_end = 0;
        for r in patches {
            let width = if r.kind == 19 || r.kind == 18 { 8 } else { 4 };
            require(
                r.offset >= previous_end,
                "duplicate or overlapping text relocation patches",
            )?;
            previous_end = end(r.offset, width)?;
            let id = symbol_id(c.object, r);
            let first = word(original, r.offset)?;
            let (resolved, place, high, low, old_words, new_words) = match r.kind {
                19 | 23 => {
                    require(first & 0x7f == 0x17, "high relocation is not AUIPC")?;
                    let resolved = target(resolver.resolve(id)?, r.addend)?;
                    let place = end(c.image.value, r.offset)?;
                    let (high, low) = halves(resolved, place)?;
                    let patched = (first & 0xfff) | (((high as u32) & 0xfffff) << 12);
                    let mut old_words = vec![first];
                    let mut new_words = vec![patched];
                    if r.kind == 19 {
                        let second = word(original, end(r.offset, 4)?)?;
                        require(
                            first >> 7 & 31 != 0
                                && second & 0x707f == 0x67
                                && (second >> 15 & 31) == (first >> 7 & 31),
                            "CALL relocation has invalid AUIPC/JALR register shape",
                        )?;
                        old_words.push(second);
                        new_words.push((second & 0xfffff) | (((low as u32) & 0xfff) << 20));
                    }
                    (resolved, place, high, low, old_words, new_words)
                }
                24 => {
                    require(r.addend == 0, "PCREL low relocation addend is not zero")?;
                    let label = indices[usize::from(c.object)].symbol(id)?;
                    require(
                        usize::from(label.section) == c.section,
                        "PCREL low label is not in the same section",
                    )?;
                    let hi = high_sites
                        .get(&(c.object, c.section, label.value))
                        .ok_or_else(|| {
                            error(
                                ErrorClass::Infrastructure,
                                "PCREL low label has no unique high relocation",
                            )
                        })?;
                    if label.binding != 0 {
                        return unsupported("nonlocal PCREL high-site label is not implemented");
                    }
                    let high_word = word(original, hi.offset)?;
                    require(
                        high_word & 0x7f == 0x17,
                        "paired high relocation is not AUIPC",
                    )?;
                    if first & 0x707f != 0x13 {
                        require(
                            legal_i_consumer(first),
                            "PCREL low relocation has an invalid I-type instruction",
                        )?;
                        return unsupported("PCREL low I-type consumer is not implemented");
                    }
                    if first >> 15 & 31 != high_word >> 7 & 31 {
                        return unsupported("PCREL low register relationship is not implemented");
                    }
                    let resolved = target(resolver.resolve(symbol_id(c.object, hi))?, hi.addend)?;
                    let place = end(c.image.value, hi.offset)?;
                    let (high, low) = halves(resolved, place)?;
                    let patched = (first & 0xfffff) | (((low as u32) & 0xfff) << 20);
                    (resolved, place, high, low, vec![first], vec![patched])
                }
                16 => return unsupported("BRANCH text relocation is not implemented"),
                17 => return unsupported("JAL text relocation is not implemented"),
                18 => return unsupported("CALL text relocation is not implemented"),
                25 => return unsupported("PCREL low S-type relocation is not implemented"),
                _ => {
                    return Err(error(
                        ErrorClass::Infrastructure,
                        "unexpected text relocation family",
                    ));
                }
            };
            for (i, value) in new_words.iter().enumerate() {
                put(&mut rebuilt, end(r.offset, (i as u64) * 4)?, *value)?;
            }
            budget.row()?;
            c.patches.push(Patch {
                relocation_section: r.section,
                offset: r.offset,
                kind: r.kind,
                symbol: id,
                addend: r.addend,
                target: resolved,
                high_site: place,
                high,
                low,
                original_words: old_words,
                linked_words: new_words,
            });
        }
        let final_section = &image.sections[usize::from(c.image.section)];
        let at = end(final_section.offset, c.image.value - final_section.address)?;
        require(
            rebuilt == bytes(linked, at, c.image.size)?,
            "whole reconstructed text differs from linked bytes",
        )?;
    }
    require(
        relocations.is_empty(),
        "text relocations have no contribution",
    )?;
    require(
        object_bytes == image_bytes,
        "object and image text coverage differ",
    )?;
    Ok(TextInspection {
        inputs: [entry, program, linked],
        contributions: output,
        text_bytes: image_bytes,
        rows: budget.rows,
    })
}
