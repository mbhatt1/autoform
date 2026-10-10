package autoform.compiler

/** Target-width tables and literal conversion, independent of CPG/session state. */
object Numeric {
  /** Integer types whose width is fixed by the **language**, not by the target.
    *
    * `long` is not here, and its absence is the point. `long` is 64 bits under LP64
    * (Linux and macOS on x86-64 and arm64) and 32 bits under LLP64 (Windows): its width
    * is a property of the target *data model*, not of C. It used to be mapped to `i32`,
    * which meant `(long)x` truncated to 32 bits on the very platforms both C corpora
    * target — a well-typed, hole-free, silently wrong translation, which is the one
    * failure mode the ledger cannot see, because a hole-free function is what it counts
    * as good. The same is true of `size_t`, `ssize_t`, `ptrdiff_t`, `intptr_t` and
    * `uintptr_t`, all of which are pointer- or target-sized; they live in
    * `modelDependentInts` below and are resolved only against a *stated* data model.
    *
    * `char` is deliberately absent for a different reason: its signedness is
    * implementation-defined, so `(char)300` has no standard-mandated value.
    *
    * The kernel's `s8`..`u64` and `__s8`..`__u64` **are** here: those spellings exist
    * precisely to name an exact width and mean the same thing on every target. `__le32`
    * and friends are not, because their value is byte-swapped as well as narrowed and
    * only the narrowing would be modelled.
    *
    * `009-reduce-remaining-holes-4` US2: `longlongint`/`unsignedlonglongint` (the
    * four-word forms) are a distinct spelling from `longlong`/`unsignedlonglong`
    * (three words) already above -- `bareType` only strips whitespace, so
    * `"long long int"` and `"long long"` never collide. SQLite's own `sqlite_int64`/
    * `sqlite_uint64` (and everything typedef'd from them: `i64`, `u64`, `Bitmask`,
    * `Pgno`, `tRowcnt`, ...) resolve to exactly the four-word form once `sqlite3.h`
    * is present in the parse (it is generated from `src/sqlite.h.in` and was
    * missing from the raw `src/`-only checkout this session's sandbox parses --
    * without it, Joern has no declaration for `sqlite_int64`/`sqlite_uint64` at
    * all and reports every alias chain through them as `ANY`). Confirmed live: a
    * local re-parse with a generated `sqlite3.h` added to the source tree resolves
    * `sqlite_int64`/`sqlite_uint64` correctly, but the alias chain still landed on
    * the missing four-word spelling until these two entries were added. */
  val intTypeNames: Map[String, String] = Map(
    "int8_t" -> "i8", "signedchar" -> "i8", "s8" -> "i8", "__s8" -> "i8",
    "uint8_t" -> "u8", "unsignedchar" -> "u8", "u8" -> "u8", "__u8" -> "u8",
    "int16_t" -> "i16", "short" -> "i16", "shortint" -> "i16", "s16" -> "i16",
    "__s16" -> "i16",
    "uint16_t" -> "u16", "unsignedshort" -> "u16", "u16" -> "u16", "__u16" -> "u16",
    "int32_t" -> "i32", "int" -> "i32", "signedint" -> "i32", "s32" -> "i32",
    "__s32" -> "i32",
    "uint32_t" -> "u32", "unsignedint" -> "u32", "unsigned" -> "u32", "u32" -> "u32",
    "__u32" -> "u32",
    "int64_t" -> "i64", "longlong" -> "i64", "longlongint" -> "i64", "s64" -> "i64",
    "__s64" -> "i64",
    "uint64_t" -> "u64", "unsignedlonglong" -> "u64", "unsignedlonglongint" -> "u64",
    "u64" -> "u64", "__u64" -> "u64"
  )

  /** Integer types whose width is a property of the **target data model**.
    *
    * Three models are tabulated. `lp64` is Linux/macOS/BSD on any 64-bit architecture and
    * is the default, because that is what both C corpora — the Linux kernel and V8 — are
    * built for. `llp64` is 64-bit Windows, where `long` stays 32 bits. `ilp32` is any
    * 32-bit target. Passing `--param dataModel=unknown` (or any unlisted name) makes every
    * one of these types a hole labelled `op:cast:model-dependent`, which is the honest
    * answer when the model is not known: the alternative is to guess a width silently,
    * and guessing a width silently is exactly the defect this table exists to remove.
    *
    * The assumption does not have to be taken on trust when reading the output: the
    * emitted operator names the width it chose, so `(long)x` under `lp64` renders as
    * `Expr.unop "cast:i64"` and under `llp64` as `"cast:i32"`. The number is in the
    * artifact, at every site. */
  val dataModelTable: Map[String, Map[String, String]] = Map(
    "lp64" -> Map(
      "long" -> "i64", "longint" -> "i64", "signedlong" -> "i64",
      "unsignedlong" -> "u64", "longunsigned" -> "u64", "unsignedlongint" -> "u64",
      "size_t" -> "u64", "ssize_t" -> "i64", "ptrdiff_t" -> "i64",
      "intptr_t" -> "i64", "uintptr_t" -> "u64"),
    "llp64" -> Map(
      "long" -> "i32", "longint" -> "i32", "signedlong" -> "i32",
      "unsignedlong" -> "u32", "longunsigned" -> "u32", "unsignedlongint" -> "u32",
      "size_t" -> "u64", "ssize_t" -> "i64", "ptrdiff_t" -> "i64",
      "intptr_t" -> "i64", "uintptr_t" -> "u64"),
    "ilp32" -> Map(
      "long" -> "i32", "longint" -> "i32", "signedlong" -> "i32",
      "unsignedlong" -> "u32", "longunsigned" -> "u32", "unsignedlongint" -> "u32",
      "size_t" -> "u32", "ssize_t" -> "i32", "ptrdiff_t" -> "i32",
      "intptr_t" -> "i32", "uintptr_t" -> "u32")
  )

  /** Every type name whose width depends on the model, whichever model is in force. */
  val modelDependentNames: Set[String] = dataModelTable.values.flatMap(_.keys).toSet
  /** Parse a C/C++/Java integer literal.
    *
    * `toIntOption` alone was the whole implementation, and on V8 it failed on 309 of the
    * literals in `src/base` — every hex constant, every `u`/`U`/`L`/`ULL` suffix, C++14
    * digit separators (`0x0010'0000'0000'0000`), binary `0b10000`, and anything past
    * 2^31. Each became a `lit:unquoted` hole, so a function containing `0xFFFFFFFF` was
    * unanalysable for want of a number.
    *
    * Returns `BigInt` because a C++ literal routinely exceeds `Int` and often exceeds
    * `Long` (`0xFFFFFFFFFFFFFFFF`). The caller emits anything beyond 2^53 as a decimal
    * *string*, since JSON numbers are doubles and would silently round it — the exact
    * class of quiet corruption this project keeps finding.
    */
  def parseIntLiteral(raw: String): Option[BigInt] = {
    val trimmed = raw.trim
    // A quoted CHARACTER literal is not an integer literal, and must not be mistaken
    // for one here: stripping every `'` turned `'0'` into `"0"` and returned 0, the
    // digit's VALUE instead of its codepoint 48. `'A'` escaped only because `"A"` is
    // not all digits, so it fell through to the character-literal branch and got 65 --
    // which is why the bug was invisible until a corpus compared both. Live-confirmed
    // on org.json's `JSONTokener.dehexchar` (3 divergences vs the JVM: `c >= '0' && c
    // <= '9'` answered on 0..9 instead of 48..57). `c >= '0' && c <= '9'` is the most
    // common character-range idiom there is, and this made it silently wrong in every
    // C, C++, Java, Kotlin and Go program. Return None and let the character-literal
    // branch below resolve the codepoint.
    if (trimmed.length >= 3 && trimmed.head == '\'' && trimmed.last == '\'') return None
    // C++14 digit separators, by the actual rule: a `'` only separates digits when it
    // sits BETWEEN two of them (`1'000'000`, `0xDE'AD'BE'EF`). Anywhere else it is
    // quoting, not separating.
    var t = trimmed.replaceAll("(?<=[0-9a-fA-F])'(?=[0-9a-fA-F])", "")
    if (t.isEmpty) return None
    var neg = false
    if (t.startsWith("-")) { neg = true; t = t.drop(1) }
    else if (t.startsWith("+")) t = t.drop(1)
    // Integer suffixes, in any order and case: 0u, 1L, 2ULL, 3llu.
    val body = t.reverse.dropWhile(ch => ch == 'u' || ch == 'U' || ch == 'l' || ch == 'L').reverse
    if (body.isEmpty) return None
    val parsed: Option[BigInt] =
      try {
        if (body.length > 2 && (body.startsWith("0x") || body.startsWith("0X")))
          Some(BigInt(body.drop(2), 16))
        else if (body.length > 2 && (body.startsWith("0b") || body.startsWith("0B")))
          Some(BigInt(body.drop(2), 2))
        // A leading zero is octal in C, but plain "0" is zero, and a decimal point or an
        // exponent means this is a float and not ours to claim.
        else if (body.length > 1 && body.head == '0' && body.forall(_.isDigit))
          Some(BigInt(body.drop(1), 8))
        else if (body.forall(_.isDigit)) Some(BigInt(body))
        else None
      } catch { case _: NumberFormatException => None }
    parsed.map(v => if (neg) -v else v)
  }

  /** JSON for an integer literal, without losing precision to a double. */
  def intLit(v: BigInt): ujson.Obj =
    if (v.abs <= BigInt(2).pow(53)) ujson.Obj("k" -> "int", "v" -> v.toLong)
    else ujson.Obj("k" -> "int", "v" -> v.toString)

  /** `010-reach-90pct-hole-free`: the integer value of a C/C++/Java/Kotlin/Go character
    * (rune) literal's INNER text (already stripped of its surrounding `'...'`) -- see
    * `charLiteralIsNumeric`'s own doc comment for why this exists at all. Handles a
    * single plain character (its Unicode codepoint -- ASCII-range C source, the
    * overwhelming common case, so codepoint IS byte value) and the standard C escape
    * sequences: `\n \t \r \0 \\ \' \" \a \b \f \v`, octal (`\NNN`, 1-3 octal digits),
    * and hex (`\xNN...`). Deliberately `None`, never a guess, for anything else --
    * a multi-character literal (`'ab'`, its value is implementation-defined even in
    * real C) or an escape this does not recognise: falls through to the existing
    * `str` treatment's own honest labelling path below, exactly like every other
    * "shape not recognised" case in this file. */
  def charLiteralValue(inner: String): Option[Long] = {
    val simpleEscapes = Map(
      "\\n" -> 10L, "\\t" -> 9L, "\\r" -> 13L, "\\0" -> 0L, "\\\\" -> 92L,
      "\\'" -> 39L, "\\\"" -> 34L, "\\a" -> 7L, "\\b" -> 8L, "\\f" -> 12L, "\\v" -> 11L
    )
    if (inner.length == 1 && inner.head != '\\') Some(inner.head.toLong)
    else if (simpleEscapes.contains(inner)) Some(simpleEscapes(inner))
    else if (inner.length >= 2 && inner.startsWith("\\x") &&
             inner.drop(2).nonEmpty && inner.drop(2).forall(ch => ch.isDigit || "abcdefABCDEF".contains(ch)))
      try Some(java.lang.Long.parseLong(inner.drop(2), 16)) catch { case _: NumberFormatException => None }
    else if (inner.length >= 2 && inner.startsWith("\\") && inner.drop(1).forall(ch => ch >= '0' && ch <= '7') &&
             inner.drop(1).length <= 3)
      try Some(java.lang.Long.parseLong(inner.drop(1), 8)) catch { case _: NumberFormatException => None }
    else None
  }

}
