/-
Copyright (c) 2020 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import data.string.basic
import data.buffer.basic
import data.nat.digits

/-!
# Parsers

`parser α` is the type that describes a computation that can ingest a `char_buffer`
and output, if successful, a term of type `α`.
This file expands on the definitions in the core library, proving that all the core library
parsers are `mono`. There are also lemmas on the composability of parsers.

## Main definitions

* `parse_result.pos` : The position of a `char_buffer` at which a `parser α` has finished.
* `parser.mono` : The property that a parser only moves forward within a buffer,
  in both cases of success or failure.

## Implementation details

Lemmas about how parsers are mono are in the `mono` namespace. That allows using projection
notation for shorter term proofs that are parallel to the definitions of the parsers in structure.

-/

open parser parse_result

/--
For some `parse_result α`, give the position at which the result was provided, in either the
`done` or the `fail` case.
-/
@[simp] def parse_result.pos {α} : parse_result α → ℕ
| (done n _) := n
| (fail n _) := n

namespace parser

section defn_lemmas

variables {α β : Type} (msgs : thunk (list string)) (msg : thunk string)
variables (p q : parser α) (cb : char_buffer) (n n' : ℕ) {err : dlist string}
variables {a : α} {b : β}

/--
A `p : parser α` is defined to be `mono` if the result `p cb n` it gives,
for some `cb : char_buffer` and `n : ℕ`, (whether `done` or `fail`),
is always at a `parse_result.pos` that is at least `n`.
The 'mono' property is mainly used to ensure proper branching in 'orelse'.
-/
class mono : Prop :=
(le' : ∀ (cb : char_buffer) (n : ℕ), n ≤ (p cb n).pos)

lemma mono.le [p.mono] : n ≤ (p cb n).pos := mono.le' cb n

/--
A `parser α` is defined to be `static` if it does not move on success.
-/
class static : Prop :=
(of_done : ∀ {cb : char_buffer} {n n' : ℕ} {a : α}, p cb n = done n' a → n = n')

/--
A `parser α` is defined to be `err_static` if it does not move on error.
-/
class err_static : Prop :=
(of_fail : ∀ {cb : char_buffer} {n n' : ℕ} {err : dlist string}, p cb n = fail n' err → n = n')

/--
A `parser α` is defined to be `prog` if it always moves forward on success.
-/
class prog : Prop :=
(of_done : ∀ {cb : char_buffer} {n n' : ℕ} {a : α}, p cb n = done n' a → n < n')

/--
A `parser a` is defined to be `bounded` if it produces a
`fail` `parse_result` when it is parsing outside the provided `char_buffer`.
-/
class bounded : Prop :=
(ex' : ∀ {cb : char_buffer} {n : ℕ}, cb.size ≤ n → ∃ (n' : ℕ) (err : dlist string),
  p cb n = fail n' err)

lemma bounded.exists (p : parser α) [p.bounded] {cb : char_buffer} {n : ℕ} (h : cb.size ≤ n) :
  ∃ (n' : ℕ) (err : dlist string), p cb n = fail n' err :=
bounded.ex' h

/--
A `parser a` is defined to be `unfailing` if it always produces a `done` `parse_result`.
-/
class unfailing : Prop :=
(ex' : ∀ (cb : char_buffer) (n : ℕ), ∃ (n' : ℕ) (a : α), p cb n = done n' a)

/--
A `parser a` is defined to be `conditionally_unfailing` if it produces a
`done` `parse_result` as long as it is parsing within the provided `char_buffer`.
-/
class conditionally_unfailing : Prop :=
(ex' : ∀ {cb : char_buffer} {n : ℕ}, n < cb.size → ∃ (n' : ℕ) (a : α), p cb n = done n' a)

lemma fail_iff :
  (∀ pos' result, p cb n ≠ done pos' result) ↔
    ∃ (pos' : ℕ) (err : dlist string), p cb n = fail pos' err :=
by cases p cb n; simp

lemma success_iff :
  (∀ pos' err, p cb n ≠ fail pos' err) ↔ ∃ (pos' : ℕ) (result : α), p cb n = done pos' result :=
by cases p cb n; simp

variables {p q cb n n' msgs msg}

lemma mono.of_done [p.mono] (h : p cb n = done n' a) : n ≤ n' :=
by simpa [h] using mono.le p cb n

lemma mono.of_fail [p.mono] (h : p cb n = fail n' err) : n ≤ n' :=
by simpa [h] using mono.le p cb n

lemma bounded.of_done [p.bounded] (h : p cb n = done n' a) : n < cb.size :=
begin
  contrapose! h,
  obtain ⟨np, err, hp⟩ := bounded.exists p h,
  simp [hp]
end

lemma static.iff :
  static p ↔ (∀ (cb : char_buffer) (n n' : ℕ) (a : α), p cb n = done n' a → n = n') :=
⟨λ h _ _ _ _ hp, by { haveI := h, exact static.of_done hp}, λ h, ⟨h⟩⟩

lemma exists_done (p : parser α) [p.unfailing] (cb : char_buffer) (n : ℕ) :
  ∃ (n' : ℕ) (a : α), p cb n = done n' a :=
unfailing.ex' cb n

lemma unfailing.of_fail [p.unfailing] (h : p cb n = fail n' err) : false :=
begin
  obtain ⟨np, a, hp⟩ := p.exists_done cb n,
  simpa [hp] using h
end

instance conditionally_unfailing_of_unfailing [p.unfailing] : conditionally_unfailing p :=
⟨λ _ _ _, p.exists_done _ _⟩

lemma exists_done_in_bounds (p : parser α) [p.conditionally_unfailing] {cb : char_buffer} {n : ℕ}
  (h : n < cb.size) : ∃ (n' : ℕ) (a : α), p cb n = done n' a :=
conditionally_unfailing.ex' h

lemma conditionally_unfailing.of_fail [p.conditionally_unfailing] (h : p cb n = fail n' err)
  (hn : n < cb.size) : false :=
begin
  obtain ⟨np, a, hp⟩ := p.exists_done_in_bounds hn,
  simpa [hp] using h
end

-- lemma prog.of_done [p.prog] (h : p cb n = done n' a) : n < n' := prog.lt' h

-- lemma bounded.of_done [p.bounded] (h : p cb n = done n' a) : n < cb.size :=
-- by { by_contra hn, exact bounded.ne' (le_of_not_lt hn) h }

-- lemma static.of_done [p.static] (h : p cb n = done n' a) : n = n' :=
-- static.eq' h

-- lemma err_static.of_fail [p.err_static] (h : p cb n = fail n' err) : n = n' :=
-- err_static.eq' h

lemma decorate_errors_fail (h : p cb n = fail n' err) :
  @decorate_errors α msgs p cb n = fail n ((dlist.lazy_of_list (msgs ()))) :=
by simp [decorate_errors, h]

lemma decorate_errors_success (h : p cb n = done n' a) :
  @decorate_errors α msgs p cb n = done n' a :=
by simp [decorate_errors, h]

lemma decorate_error_fail (h : p cb n = fail n' err) :
  @decorate_error α msg p cb n = fail n ((dlist.lazy_of_list ([msg ()]))) :=
decorate_errors_fail h

lemma decorate_error_success (h : p cb n = done n' a) :
  @decorate_error α msg p cb n = done n' a :=
decorate_errors_success h

@[simp] lemma decorate_errors_eq_done :
  @decorate_errors α msgs p cb n = done n' a ↔ p cb n = done n' a :=
by cases h : p cb n; simp [decorate_errors, h]

@[simp] lemma decorate_error_eq_done :
  @decorate_error α msg p cb n = done n' a ↔ p cb n = done n' a :=
decorate_errors_eq_done

@[simp] lemma decorate_errors_eq_fail :
  @decorate_errors α msgs p cb n = fail n' err ↔
    n = n' ∧ err = dlist.lazy_of_list (msgs ()) ∧ ∃ np err', p cb n = fail np err' :=
by cases h : p cb n; simp [decorate_errors, h, eq_comm]

@[simp] lemma decorate_error_eq_fail :
  @decorate_error α msg p cb n = fail n' err ↔
    n = n' ∧ err = dlist.lazy_of_list ([msg ()]) ∧ ∃ np err', p cb n = fail np err' :=
decorate_errors_eq_fail

@[simp] lemma return_eq_pure : (@return parser _ _ a) = pure a := rfl

lemma pure_eq_done : (@pure parser _ _ a) = λ _ n, done n a := rfl

@[simp] lemma pure_ne_fail : (pure a : parser α) cb n ≠ fail n' err := by simp [pure_eq_done]

section bind

variable (f : α → parser β)

@[simp] lemma bind_eq_bind : p.bind f = p >>= f := rfl

variable {f}

@[simp] lemma bind_eq_done :
  (p >>= f) cb n = done n' b ↔
  ∃ (np : ℕ) (a : α), p cb n = done np a ∧ f a cb np = done n' b :=
by cases hp : p cb n; simp [hp, ←bind_eq_bind, parser.bind, and_assoc]

@[simp] lemma bind_eq_fail :
  (p >>= f) cb n = fail n' err ↔
  (p cb n = fail n' err) ∨ (∃ (np : ℕ) (a : α), p cb n = done np a ∧ f a cb np = fail n' err) :=
by cases hp : p cb n; simp [hp, ←bind_eq_bind, parser.bind, and_assoc]

@[simp] lemma and_then_eq_bind {α β : Type} {m : Type → Type} [monad m] (a : m α) (b : m β) :
  a >> b = a >>= (λ _, b) := rfl

lemma and_then_fail :
  (p >> return ()) cb n = parse_result.fail n' err ↔ p cb n = fail n' err :=
by simp [pure_eq_done]

lemma and_then_success :
  (p >> return ()) cb n = parse_result.done n' () ↔ ∃ a, p cb n = done n' a:=
by simp [pure_eq_done]

end bind

section map

variable {f : α → β}

@[simp] lemma map_eq_done : (f <$> p) cb n = done n' b ↔
  ∃ (a : α), p cb n = done n' a ∧ f a = b :=
by cases hp : p cb n; simp [←is_lawful_monad.bind_pure_comp_eq_map, hp, and_assoc, pure_eq_done]

@[simp] lemma map_eq_fail : (f <$> p) cb n = fail n' err ↔ p cb n = fail n' err :=
by simp [←bind_pure_comp_eq_map, pure_eq_done]

@[simp] lemma map_const_eq_done {b'} : (b <$ p) cb n = done n' b' ↔
  ∃ (a : α), p cb n = done n' a ∧ b = b' :=
by simp [map_const_eq]

@[simp] lemma map_const_eq_fail : (b <$ p) cb n = fail n' err ↔ p cb n = fail n' err :=
by simp only [map_const_eq, map_eq_fail]

lemma map_const_rev_eq_done {b'} : (p $> b) cb n = done n' b' ↔
  ∃ (a : α), p cb n = done n' a ∧ b = b' :=
map_const_eq_done

lemma map_rev_const_eq_fail : (p $> b) cb n = fail n' err ↔ p cb n = fail n' err :=
map_const_eq_fail

end map

@[simp] lemma orelse_eq_orelse : p.orelse q = (p <|> q) := rfl

@[simp] lemma orelse_eq_done : (p <|> q) cb n = done n' a ↔
  (p cb n = done n' a ∨ (q cb n = done n' a ∧ ∃ err, p cb n = fail n err)) :=
begin
  cases hp : p cb n with np resp np errp,
  { simp [hp, ←orelse_eq_orelse, parser.orelse] },
  { by_cases hn : np = n,
    { cases hq : q cb n with nq resq nq errq,
      { simp [hp, hn, hq, ←orelse_eq_orelse, parser.orelse] },
      { rcases lt_trichotomy nq n with H|rfl|H;
        simp [hp, hn, hq, H, not_lt_of_lt H, lt_irrefl, ←orelse_eq_orelse, parser.orelse] <|>
          simp [hp, hn, hq, lt_irrefl, ←orelse_eq_orelse, parser.orelse] } },
    { simp [hp, hn, ←orelse_eq_orelse, parser.orelse] } }
end

@[simp] lemma orelse_eq_fail_eq : (p <|> q) cb n = fail n err ↔
  (p cb n = fail n err ∧ ∃ (nq errq), n < nq ∧ q cb n = fail nq errq) ∨
  (∃ (errp errq), p cb n = fail n errp ∧ q cb n = fail n errq ∧ errp ++ errq = err)
 :=
begin
  cases hp : p cb n with np resp np errp,
  { simp [hp, ←orelse_eq_orelse, parser.orelse] },
  { by_cases hn : np = n,
    { cases hq : q cb n with nq resq nq errq,
      { simp [hp, hn, hq, ←orelse_eq_orelse, parser.orelse] },
      { rcases lt_trichotomy nq n with H|rfl|H;
        simp [hp, hq, hn, ←orelse_eq_orelse, parser.orelse, H,
              ne_of_gt H, ne_of_lt H, not_lt_of_lt H] <|>
          simp [hp, hq, hn, ←orelse_eq_orelse, parser.orelse, lt_irrefl] } },
    { simp [hp, hn, ←orelse_eq_orelse, parser.orelse] } }
end

lemma orelse_eq_fail_not_mono_lt (hn : n' < n) : (p <|> q) cb n = fail n' err ↔
  (p cb n = fail n' err) ∨
  (q cb n = fail n' err ∧ (∃ (errp), p cb n = fail n errp)) :=
begin
  cases hp : p cb n with np resp np errp,
  { simp [hp, ←orelse_eq_orelse, parser.orelse] },
  { by_cases h : np = n,
    { cases hq : q cb n with nq resq nq errq,
      { simp [hp, h, hn, hq, ne_of_gt hn, ←orelse_eq_orelse, parser.orelse] },
      { rcases lt_trichotomy nq n with H|H|H,
        { simp [hp, hq, h, H, ne_of_gt hn, not_lt_of_lt H, ←orelse_eq_orelse, parser.orelse] },
        { simp [hp, hq, h, H, ne_of_gt hn, lt_irrefl, ←orelse_eq_orelse, parser.orelse] },
        { simp [hp, hq, h, H, ne_of_gt (hn.trans H), ←orelse_eq_orelse, parser.orelse] } } },
    { simp [hp, h, ←orelse_eq_orelse, parser.orelse] } }
end

lemma orelse_eq_fail_of_mono_ne [q.mono] (hn : n ≠ n') :
  (p <|> q) cb n = fail n' err ↔ p cb n = fail n' err :=
begin
  cases hp : p cb n with np resp np errp,
  { simp [hp, ←orelse_eq_orelse, parser.orelse] },
  { by_cases h : np = n,
    { cases hq : q cb n with nq resq nq errq,
      { simp [hp, h, hn, hq, hn, ←orelse_eq_orelse, parser.orelse] },
      { have : n ≤ nq := mono.of_fail hq,
        rcases eq_or_lt_of_le this with rfl|H,
        { simp [hp, hq, h, hn, lt_irrefl, ←orelse_eq_orelse, parser.orelse] },
        { simp [hp, hq, h, hn, H, ←orelse_eq_orelse, parser.orelse] } } },
    { simp [hp, h, ←orelse_eq_orelse, parser.orelse] } },
end

@[simp] lemma failure_eq_failure : @parser.failure α = failure := rfl

@[simp] lemma failure_def : (failure : parser α) cb n = fail n dlist.empty := rfl

lemma not_failure_eq_done : ¬ (failure : parser α) cb n = done n' a :=
by simp

lemma failure_eq_fail : (failure : parser α) cb n = fail n' err ↔ n = n' ∧ err = dlist.empty :=
by simp [eq_comm]

lemma seq_eq_done {f : parser (α → β)} {p : parser α} : (f <*> p) cb n = done n' b ↔
  ∃ (nf : ℕ) (f' : α → β) (a : α), f cb n = done nf f' ∧ p cb nf = done n' a ∧ f' a = b :=
by simp [seq_eq_bind_map]

lemma seq_eq_fail {f : parser (α → β)} {p : parser α} : (f <*> p) cb n = fail n' err ↔
  (f cb n = fail n' err) ∨ (∃ (nf : ℕ) (f' : α → β), f cb n = done nf f' ∧ p cb nf = fail n' err) :=
by simp [seq_eq_bind_map]

lemma seq_left_eq_done {p : parser α} {q : parser β} : (p <* q) cb n = done n' a ↔
  ∃ (np : ℕ) (b : β), p cb n = done np a ∧ q cb np = done n' b :=
begin
  have : ∀ (p q : ℕ → α → Prop),
    (∃ (np : ℕ) (x : α), p np x ∧ q np x ∧ x = a) ↔ ∃ (np : ℕ), p np a ∧ q np a :=
    λ _ _, ⟨λ ⟨np, x, hp, hq, rfl⟩, ⟨np, hp, hq⟩, λ ⟨np, hp, hq⟩, ⟨np, a, hp, hq, rfl⟩⟩,
  simp [seq_left_eq, seq_eq_done, map_eq_done, this]
end

lemma seq_left_eq_fail {p : parser α} {q : parser β} : (p <* q) cb n = fail n' err ↔
  (p cb n = fail n' err) ∨ (∃ (np : ℕ) (a : α), p cb n = done np a ∧ q cb np = fail n' err) :=
by simp [seq_left_eq, seq_eq_fail]

lemma seq_right_eq_done {p : parser α} {q : parser β} : (p *> q) cb n = done n' b ↔
  ∃ (np : ℕ) (a : α), p cb n = done np a ∧ q cb np = done n' b :=
by simp [seq_right_eq, seq_eq_done, map_eq_done, and.comm, and.assoc]

lemma seq_right_eq_fail {p : parser α} {q : parser β} : (p *> q) cb n = fail n' err ↔
  (p cb n = fail n' err) ∨ (∃ (np : ℕ) (a : α), p cb n = done np a ∧ q cb np = fail n' err) :=
by simp [seq_right_eq, seq_eq_fail]

lemma mmap_eq_done {f : α → parser β} {a : α} {l : list α} {b : β} {l' : list β} :
  (a :: l).mmap f cb n = done n' (b :: l') ↔
  ∃ (np : ℕ), f a cb n = done np b ∧ l.mmap f cb np = done n' l' :=
by simp [mmap, and.comm, and.assoc, and.left_comm, pure_eq_done]

lemma mmap'_eq_done {f : α → parser β} {a : α} {l : list α} :
  (a :: l).mmap' f cb n = done n' () ↔
  ∃ (np : ℕ) (b : β), f a cb n = done np b ∧ l.mmap' f cb np = done n' () :=
by simp [mmap']

lemma guard_eq_done {p : Prop} [decidable p] {u : unit} :
  @guard parser _ p _ cb n = done n' u ↔ p ∧ n = n' :=
by { by_cases hp : p; simp [guard, hp, pure_eq_done] }

lemma guard_eq_fail {p : Prop} [decidable p] :
  @guard parser _ p _ cb n = fail n' err ↔ (¬ p) ∧ n = n' ∧ err = dlist.empty :=
by { by_cases hp : p; simp [guard, hp, eq_comm, pure_eq_done] }

namespace mono

variables {sep : parser unit}

instance pure : mono (pure a) :=
⟨λ _ _, by simp [pure_eq_done]⟩

instance bind {f : α → parser β} [p.mono] [∀ a, (f a).mono] :
  (p >>= f).mono :=
begin
  constructor,
  intros cb n,
  cases hx : (p >>= f) cb n,
  { obtain ⟨n', a, h, h'⟩ := bind_eq_done.mp hx,
    refine le_trans (of_done h) _,
    simpa [h'] using of_done h' },
  { obtain h | ⟨n', a, h, h'⟩ := bind_eq_fail.mp hx,
    { simpa [h] using of_fail h },
    { refine le_trans (of_done h) _,
      simpa [h'] using of_fail h' } }
end

instance and_then {q : parser β} [p.mono] [q.mono] : (p >> q).mono := mono.bind

instance map [p.mono] {f : α → β} : (f <$> p).mono := mono.bind

instance seq {f : parser (α → β)} [f.mono] [p.mono] : (f <*> p).mono := mono.bind

instance mmap : Π {l : list α} {f : α → parser β} [∀ a ∈ l, (f a).mono],
  (l.mmap f).mono
| []       _ _ := mono.pure
| (a :: l) f h := begin
  convert mono.bind,
  { exact h _ (list.mem_cons_self _ _) },
  { intro,
    convert mono.map,
    convert mmap,
    exact (λ _ ha, h _ (list.mem_cons_of_mem _ ha)) }
end

instance mmap' : Π {l : list α} {f : α → parser β} [∀ a ∈ l, (f a).mono],
  (l.mmap' f).mono
| []       _ _ := mono.pure
| (a :: l) f h := begin
  convert mono.and_then,
  { exact h _ (list.mem_cons_self _ _) },
  { convert mmap',
    exact (λ _ ha, h _ (list.mem_cons_of_mem _ ha)) }
end

instance failure : (failure : parser α).mono :=
⟨by simp [le_refl]⟩

instance guard {p : Prop} [decidable p] : mono (guard p) :=
⟨by { by_cases h : p; simp [h, pure_eq_done, le_refl] }⟩

instance orelse [p.mono] [q.mono] : (p <|> q).mono :=
begin
  constructor,
  intros cb n,
  cases hx : (p <|> q) cb n with posx resx posx errx,
  { obtain h | ⟨h, -, -⟩ := orelse_eq_done.mp hx;
    simpa [h] using of_done h },
  { by_cases h : n = posx,
    { simp [hx, h] },
    { simp [orelse_eq_fail_of_mono_ne h, of_fail] at hx,
      exact of_fail hx } }
end

instance decorate_errors [p.mono] :
  (@decorate_errors α msgs p).mono :=
begin
  constructor,
  intros cb n,
  cases h : p cb n,
  { simpa [decorate_errors, h] using of_done h },
  { simp [decorate_errors, h] }
end

instance decorate_error [p.mono] : (@decorate_error α msg p).mono :=
mono.decorate_errors

instance any_char : mono any_char :=
begin
  constructor,
  intros cb n,
  by_cases h : n < cb.size;
  simp [any_char, h],
end

instance sat {p : char → Prop} [decidable_pred p] : mono (sat p) :=
begin
  constructor,
  intros cb n,
  simp only [sat],
  split_ifs;
  simp
end

instance eps : mono eps := mono.pure

instance ch {c : char} : mono (ch c) := mono.decorate_error

instance char_buf {s : char_buffer} : mono (char_buf s) :=
mono.decorate_error

instance one_of {cs : list char} : (one_of cs).mono :=
mono.decorate_errors

instance one_of' {cs : list char} : (one_of' cs).mono :=
mono.and_then

instance str {s : string} : (str s).mono :=
mono.decorate_error

instance remaining : remaining.mono :=
⟨λ _ _, le_refl _⟩

instance eof : eof.mono :=
mono.decorate_error

instance foldr_core {f : α → β → β} {b : β} [p.mono] :
  ∀ {reps : ℕ}, (foldr_core f p b reps).mono
| 0          := mono.failure
| (reps + 1) := begin
  convert mono.orelse,
  { convert mono.bind,
    { apply_instance },
    { exact λ _, @mono.bind _ _ _ _ foldr_core _ } },
  { exact mono.pure }
end

instance foldr {f : α → β → β} [p.mono] : mono (foldr f p b) :=
⟨λ _ _, by { convert mono.le (foldr_core f p b _) _ _, exact mono.foldr_core }⟩

instance foldl_core {f : α → β → α} {p : parser β} [p.mono] :
  ∀ {a : α} {reps : ℕ}, (foldl_core f a p reps).mono
| _ 0          := mono.failure
| _ (reps + 1) := begin
  convert mono.orelse,
  { convert mono.bind,
    { apply_instance },
    { exact λ _, foldl_core } },
  { exact mono.pure }
end

instance foldl {f : α → β → α} {p : parser β} [p.mono] : mono (foldl f a p) :=
⟨λ _ _, by { convert mono.le (foldl_core f a p _) _ _, exact mono.foldl_core }⟩

instance many [p.mono] : p.many.mono :=
mono.foldr

instance many_char {p : parser char} [p.mono] : p.many_char.mono :=
mono.map

instance many' [p.mono] : p.many'.mono :=
mono.and_then

instance many1 [p.mono] : p.many1.mono :=
mono.seq

instance many_char1 {p : parser char} [p.mono] : p.many_char1.mono :=
mono.map

instance sep_by1 [p.mono] [sep.mono] : mono (sep_by1 sep p) :=
mono.seq

instance sep_by [p.mono] [hs : sep.mono] : mono (sep_by sep p) :=
mono.orelse

lemma fix_core {F : parser α → parser α} (hF : ∀ (p : parser α), p.mono → (F p).mono) :
  ∀ (max_depth : ℕ), mono (fix_core F max_depth)
| 0               := mono.failure
| (max_depth + 1) := hF _ (fix_core _)

instance digit : digit.mono :=
mono.decorate_error

instance nat : nat.mono :=
mono.decorate_error

lemma fix {F : parser α → parser α} (hF : ∀ (p : parser α), p.mono → (F p).mono) :
  mono (fix F) :=
⟨λ _ _, by { convert mono.le (parser.fix_core F _) _ _, exact fix_core hF _ }⟩

end mono

@[simp] lemma orelse_pure_eq_fail : (p <|> pure a) cb n = fail n' err ↔
  p cb n = fail n' err ∧ n ≠ n' :=
begin
  by_cases hn : n = n',
  { simp [hn, pure_eq_done] },
  { simp [orelse_eq_fail_of_mono_ne, hn] }
end

end defn_lemmas

section done

variables {α β : Type} {cb : char_buffer} {n n' : ℕ} {a a' : α} {b : β} {c : char} {u : unit}
  {err : dlist string}

lemma any_char_eq_done : any_char cb n = done n' c ↔
  ∃ (hn : n < cb.size), n' = n + 1 ∧ cb.read ⟨n, hn⟩ = c :=
begin
  simp_rw [any_char],
  split_ifs with h;
  simp [h, eq_comm]
end

lemma any_char_eq_fail : any_char cb n = fail n' err ↔ n = n' ∧ err = dlist.empty ∧ cb.size ≤ n :=
begin
  simp_rw [any_char],
  split_ifs with h;
  simp [←not_lt, h, eq_comm]
end

lemma sat_eq_done {p : char → Prop} [decidable_pred p] : sat p cb n = done n' c ↔
  ∃ (hn : n < cb.size), p c ∧ n' = n + 1 ∧ cb.read ⟨n, hn⟩ = c :=
begin
  by_cases hn : n < cb.size,
  { by_cases hp : p (cb.read ⟨n, hn⟩),
    { simp only [sat, hn, hp, dif_pos, if_true, exists_prop_of_true],
      split,
      { rintro ⟨rfl, rfl⟩, simp [hp] },
      { rintro ⟨-, rfl, rfl⟩, simp } },
    { simp only [sat, hn, hp, dif_pos, false_iff, not_and, exists_prop_of_true, if_false],
      rintro H - rfl,
      exact hp H } },
  { simp [sat, hn] }
end

lemma sat_eq_fail {p : char → Prop} [decidable_pred p] : sat p cb n = fail n' err ↔
  n = n' ∧ err = dlist.empty ∧ ∀ (h : n < cb.size), ¬ p (cb.read ⟨n, h⟩) :=
begin
  dsimp only [sat],
  split_ifs;
  simp [*, eq_comm]
end

lemma eps_eq_done : eps cb n = done n' u ↔ n = n' := by simp [eps, pure_eq_done]

lemma ch_eq_done : ch c cb n = done n' u ↔ ∃ (hn : n < cb.size), n' = n + 1 ∧ cb.read ⟨n, hn⟩ = c :=
by simp [ch, eps_eq_done, sat_eq_done, and.comm, @eq_comm _ n']

lemma char_buf_eq_done {cb' : char_buffer} : char_buf cb' cb n = done n' u ↔
  n + cb'.size = n' ∧ cb'.to_list <+: (cb.to_list.drop n) :=
begin
  simp only [char_buf, decorate_error_eq_done, ne.def, ←buffer.length_to_list],
  induction cb'.to_list with hd tl hl generalizing cb n n',
  { simp [pure_eq_done, mmap'_eq_done, -buffer.length_to_list, list.nil_prefix] },
  { simp only [ch_eq_done, and.comm, and.assoc, and.left_comm, hl, mmap', and_then_eq_bind,
               bind_eq_done, list.length, exists_and_distrib_left, exists_const],
    split,
    { rintro ⟨np, h, rfl, rfl, hn, rfl⟩,
      simp only [add_comm, add_left_comm, h, true_and, eq_self_iff_true, and_true],
      have : n < cb.to_list.length := by simpa using hn,
      rwa [←buffer.nth_le_to_list _ this, ←list.cons_nth_le_drop_succ this, list.prefix_cons_inj] },
    { rintro ⟨h, rfl⟩,
      rw [list.prefix_cons_iff, list.tail_drop] at h,
      by_cases hn : n < cb.size,
      { have : n < cb.to_list.length := by simpa using hn,
        rw ←list.cons_nth_le_drop_succ this at h,
        use [n + 1, h.right],
        simpa [add_comm, add_left_comm, add_assoc, hn] using h.left },
      { have : cb.to_list.length ≤ n := by simpa using hn,
        rw list.drop_eq_nil_of_le this at h,
        simpa using h } } }
end

lemma one_of_eq_done {cs : list char} : one_of cs cb n = done n' c ↔
  ∃ (hn : n < cb.size), c ∈ cs ∧ n' = n + 1 ∧ cb.read ⟨n, hn⟩ = c :=
by simp [one_of, sat_eq_done]

lemma one_of'_eq_done {cs : list char} : one_of' cs cb n = done n' u ↔
  ∃ (hn : n < cb.size), cb.read ⟨n, hn⟩ ∈ cs ∧ n' = n + 1 :=
begin
  simp only [one_of', one_of_eq_done, eps_eq_done, and.comm, and_then_eq_bind, bind_eq_done,
             exists_eq_left, exists_and_distrib_left],
  split,
  { rintro ⟨c, hc, rfl, hn, rfl⟩,
    exact ⟨rfl, hn, hc⟩ },
  { rintro ⟨rfl, hn, hc⟩,
    exact ⟨cb.read ⟨n, hn⟩, hc, rfl, hn, rfl⟩ }
end

lemma str_eq_char_buf (s : string) : str s = char_buf s.to_list.to_buffer :=
begin
  ext cb n,
  rw [str, char_buf],
  congr,
  { simp [buffer.to_string, string.as_string_inv_to_list] },
  { simp }
end

lemma str_eq_done {s : string} : str s cb n = done n' u ↔
  n + s.length = n' ∧ s.to_list <+: (cb.to_list.drop n) :=
by simp [str_eq_char_buf, char_buf_eq_done]

lemma remaining_eq_done {r : ℕ} : remaining cb n = done n' r ↔ n = n' ∧ cb.size - n = r :=
by simp [remaining]

lemma remaining_ne_fail : remaining cb n ≠ fail n' err :=
by simp [remaining]

lemma eof_eq_done {u : unit} : eof cb n = done n' u ↔ n = n' ∧ cb.size ≤ n :=
by simp [eof, guard_eq_done, remaining_eq_done, nat.sub_eq_zero_iff_le, and_comm, and_assoc]

@[simp] lemma foldr_core_zero_eq_done {f : α → β → β} {p : parser α} {b' : β} :
  foldr_core f p b 0 cb n ≠ done n' b' :=
by simp [foldr_core]

lemma foldr_core_eq_done {f : α → β → β} {p : parser α} {reps : ℕ} {b' : β} :
  foldr_core f p b (reps + 1) cb n = done n' b' ↔
  (∃ (np : ℕ) (a : α) (xs : β), p cb n = done np a ∧ foldr_core f p b reps cb np = done n' xs
    ∧ f a xs = b') ∨
  (n = n' ∧ b = b' ∧ ∃ (err), (p cb n = fail n err) ∨
    (∃ (np : ℕ) (a : α), p cb n = done np a ∧ foldr_core f p b reps cb np = fail n err)) :=
by simp [foldr_core, and.comm, and.assoc, pure_eq_done]

@[simp] lemma foldr_core_zero_eq_fail {f : α → β → β} {p : parser α} {err : dlist string} :
  foldr_core f p b 0 cb n = fail n' err ↔ n = n' ∧ err = dlist.empty :=
by simp [foldr_core, eq_comm]

lemma foldr_core_succ_eq_fail {f : α → β → β} {p : parser α} {reps : ℕ} {err : dlist string} :
  foldr_core f p b (reps + 1) cb n = fail n' err ↔ n ≠ n' ∧
  (p cb n = fail n' err ∨
    ∃ (np : ℕ) (a : α), p cb n = done np a ∧ foldr_core f p b reps cb np = fail n' err) :=
by simp [foldr_core, and_comm]

lemma foldr_eq_done {f : α → β → β} {p : parser α} {b' : β} :
  foldr f p b cb n = done n' b' ↔
  ((∃ (np : ℕ) (a : α) (x : β), p cb n = done np a ∧
    foldr_core f p b (cb.size - n) cb np = done n' x ∧ f a x = b') ∨
  (n = n' ∧ b = b' ∧ (∃ (err), p cb n = parse_result.fail n err ∨
    ∃ (np : ℕ) (x : α), p cb n = done np x ∧ foldr_core f p b (cb.size - n) cb np = fail n err))) :=
by simp [foldr, foldr_core_eq_done]

lemma foldr_eq_fail_iff_mono_at_end {f : α → β → β} {p : parser α} {err : dlist string}
  [p.mono] (hc : cb.size ≤ n) : foldr f p b cb n = fail n' err ↔
    n < n' ∧ (p cb n = fail n' err ∨ ∃ (a : α), p cb n = done n' a ∧ err = dlist.empty) :=
begin
  have : cb.size - n = 0 := nat.sub_eq_zero_of_le hc,
  simp only [foldr, foldr_core_succ_eq_fail, this, and.left_comm, foldr_core_zero_eq_fail,
             ne_iff_lt_iff_le, exists_and_distrib_right, exists_eq_left, and.congr_left_iff,
             exists_and_distrib_left],
  rintro (h | ⟨⟨a, h⟩, rfl⟩),
  { exact mono.of_fail h },
  { exact mono.of_done h }
end

lemma foldr_eq_fail {f : α → β → β} {p : parser α} {err : dlist string} :
  foldr f p b cb n = fail n' err ↔ n ≠ n' ∧ (p cb n = fail n' err ∨
    ∃ (np : ℕ) (a : α), p cb n = done np a ∧ foldr_core f p b (cb.size - n) cb np = fail n' err) :=
by simp [foldr, foldr_core_succ_eq_fail]

@[simp] lemma foldl_core_zero_eq_done {f : β → α → β} {p : parser α} {b' : β} :
  foldl_core f b p 0 cb n = done n' b' ↔ false :=
by simp [foldl_core]

lemma foldl_core_eq_done {f : β → α → β} {p : parser α} {reps : ℕ} {b' : β} :
  foldl_core f b p (reps + 1) cb n = done n' b' ↔
  (∃ (np : ℕ) (a : α), p cb n = done np a ∧ foldl_core f (f b a) p reps cb np = done n' b') ∨
  (n = n' ∧ b = b' ∧ ∃ (err), (p cb n = fail n err) ∨
    (∃ (np : ℕ) (a : α), p cb n = done np a ∧ foldl_core f (f b a) p reps cb np = fail n err)) :=
by simp [foldl_core, and.assoc, pure_eq_done]

@[simp] lemma foldl_core_zero_eq_fail {f : β → α → β} {p : parser α} {err : dlist string} :
  foldl_core f b p 0 cb n = fail n' err ↔ n = n' ∧ err = dlist.empty :=
by simp [foldl_core, eq_comm]

lemma foldl_core_succ_eq_fail {f : β → α → β} {p : parser α} {reps : ℕ} {err : dlist string} :
  foldl_core f b p (reps + 1) cb n = fail n' err ↔ n ≠ n' ∧
  (p cb n = fail n' err ∨
    ∃ (np : ℕ) (a : α), p cb n = done np a ∧ foldl_core f (f b a) p reps cb np = fail n' err) :=
by  simp [foldl_core, and_comm]

lemma foldl_eq_done {f : β → α → β} {p : parser α} {b' : β} :
  foldl f b p cb n = done n' b' ↔
  (∃ (np : ℕ) (a : α), p cb n = done np a ∧
    foldl_core f (f b a) p (cb.size - n) cb np = done n' b') ∨
  (n = n' ∧ b = b' ∧ ∃ (err), (p cb n = fail n err) ∨
    (∃ (np : ℕ) (a : α), p cb n = done np a ∧
      foldl_core f (f b a) p (cb.size - n) cb np = fail n err)) :=
by simp [foldl, foldl_core_eq_done]

lemma foldl_eq_fail {f : β → α → β} {p : parser α} {err : dlist string} :
  foldl f b p cb n = fail n' err ↔ n ≠ n' ∧ (p cb n = fail n' err ∨
    ∃ (np : ℕ) (a : α), p cb n = done np a ∧
    foldl_core f (f b a) p (cb.size - n) cb np = fail n' err) :=
by simp [foldl, foldl_core_succ_eq_fail]

lemma foldl_eq_fail_iff_mono_at_end {f : β → α → β} {p : parser α} {err : dlist string}
  [p.mono] (hc : cb.size ≤ n) : foldl f b p cb n = fail n' err ↔
    n < n' ∧ (p cb n = fail n' err ∨ ∃ (a : α), p cb n = done n' a ∧ err = dlist.empty) :=
begin
  have : cb.size - n = 0 := nat.sub_eq_zero_of_le hc,
  simp only [foldl, foldl_core_succ_eq_fail, this, and.left_comm, ne_iff_lt_iff_le, exists_eq_left,
             exists_and_distrib_right, and.congr_left_iff, exists_and_distrib_left,
             foldl_core_zero_eq_fail],
  rintro (h | ⟨⟨a, h⟩, rfl⟩),
  { exact mono.of_fail h },
  { exact mono.of_done h }
end

lemma many_eq_done_nil {p : parser α} : many p cb n = done n' (@list.nil α) ↔ n = n' ∧
  ∃ (err), p cb n = fail n err ∨ ∃ (np : ℕ) (a : α), p cb n = done np a ∧
    foldr_core list.cons p [] (cb.size - n) cb np = fail n err :=
by simp [many, foldr_eq_done]

lemma many_eq_done {p : parser α} {x : α} {xs : list α} :
  many p cb n = done n' (x :: xs) ↔ ∃ (np : ℕ), p cb n = done np x
    ∧ foldr_core list.cons p [] (cb.size - n) cb np = done n' xs :=
by simp [many, foldr_eq_done, and.comm, and.assoc, and.left_comm]

lemma many_eq_fail {p : parser α} {err : dlist string} :
  many p cb n = fail n' err ↔ n ≠ n' ∧ (p cb n = fail n' err ∨
    ∃ (np : ℕ) (a : α), p cb n = done np a ∧
      foldr_core list.cons p [] (cb.size - n) cb np = fail n' err) :=
by simp [many, foldr_eq_fail]

lemma many_char_eq_done_empty {p : parser char} : many_char p cb n = done n' string.empty ↔ n = n' ∧
  ∃ (err), p cb n = fail n err ∨ ∃ (np : ℕ) (c : char), p cb n = done np c ∧
    foldr_core list.cons p [] (cb.size - n) cb np = fail n err :=
by simp [many_char, many_eq_done_nil, map_eq_done, list.as_string_eq]

lemma many_char_eq_done_not_empty {p : parser char} {s : string} (h : s ≠ "") :
  many_char p cb n = done n' s ↔ ∃ (np : ℕ), p cb n = done np s.head ∧
    foldr_core list.cons p list.nil (buffer.size cb - n) cb np = done n' (s.popn 1).to_list :=
by simp [many_char, list.as_string_eq, string.to_list_nonempty h, many_eq_done]

lemma many_char_eq_many_of_to_list {p : parser char} {s : string} :
  many_char p cb n = done n' s ↔ many p cb n = done n' s.to_list :=
by simp [many_char, list.as_string_eq]

lemma many'_eq_done {p : parser α} : many' p cb n = done n' u ↔
  many p cb n = done n' [] ∨ ∃ (np : ℕ) (a : α) (l : list α), many p cb n = done n' (a :: l)
    ∧ p cb n = done np a ∧ foldr_core list.cons p [] (buffer.size cb - n) cb np = done n' l :=
begin
  simp only [many', eps_eq_done, many, foldr, and_then_eq_bind, exists_and_distrib_right,
             bind_eq_done, exists_eq_right],
  split,
  { rintro ⟨_ | ⟨hd, tl⟩, hl⟩,
    { exact or.inl hl },
    { have hl2 := hl,
      simp only [foldr_core_eq_done, or_false, exists_and_distrib_left, and_false, false_and,
                 exists_eq_right_right] at hl,
      obtain ⟨np, hp, h⟩ := hl,
      refine or.inr ⟨np, _, _, hl2, hp, h⟩ } },
  { rintro (h | ⟨np, a, l, hp, h⟩),
    { exact ⟨[], h⟩ },
    { refine ⟨a :: l, hp⟩ } }
end

@[simp] lemma many1_ne_done_nil {p : parser α} : many1 p cb n ≠ done n' [] :=
by simp [many1, seq_eq_done]

lemma many1_eq_done {p : parser α} {l : list α} : many1 p cb n = done n' (a :: l) ↔
  ∃ (np : ℕ), p cb n = done np a ∧ many p cb np = done n' l :=
by simp [many1, seq_eq_done, map_eq_done]

lemma many1_eq_fail {p : parser α} {err : dlist string} : many1 p cb n = fail n' err ↔
  p cb n = fail n' err ∨ (∃ (np : ℕ) (a : α), p cb n = done np a ∧ many p cb np = fail n' err) :=
by simp [many1, seq_eq_fail]

@[simp] lemma many_char1_ne_empty {p : parser char} : many_char1 p cb n ≠ done n' "" :=
by simp [many_char1, ←string.nil_as_string_eq_empty]

lemma many_char1_eq_done {p : parser char} {s : string} (h : s ≠ "") :
  many_char1 p cb n = done n' s ↔
  ∃ (np : ℕ), p cb n = done np s.head ∧ many_char p cb np = done n' (s.popn 1) :=
by simp [many_char1, list.as_string_eq, string.to_list_nonempty h, many1_eq_done,
         many_char_eq_many_of_to_list]

@[simp] lemma sep_by1_ne_done_nil {sep : parser unit} {p : parser α} :
  sep_by1 sep p cb n ≠ done n' [] :=
by simp [sep_by1, seq_eq_done]

lemma sep_by1_eq_done {sep : parser unit} {p : parser α} {l : list α} :
  sep_by1 sep p cb n = done n' (a :: l) ↔ ∃ (np : ℕ), p cb n = done np a ∧
    (sep >> p).many cb np  = done n' l :=
by simp [sep_by1, seq_eq_done]

lemma sep_by_eq_done_nil {sep : parser unit} {p : parser α} :
  sep_by sep p cb n = done n' [] ↔ n = n' ∧ ∃ (err), sep_by1 sep p cb n = fail n err :=
by simp [sep_by, pure_eq_done]

@[simp] lemma fix_core_ne_done_zero {F : parser α → parser α} :
  fix_core F 0 cb n ≠ done n' a :=
by simp [fix_core]

lemma fix_core_eq_done {F : parser α → parser α} {max_depth : ℕ} :
  fix_core F (max_depth + 1) cb n = done n' a ↔ F (fix_core F max_depth) cb n = done n' a :=
by simp [fix_core]

lemma digit_eq_done {k : ℕ} : digit cb n = done n' k ↔ ∃ (hn : n < cb.size), n' = n + 1 ∧ k ≤ 9 ∧
  (cb.read ⟨n, hn⟩).to_nat - '0'.to_nat = k ∧ '0' ≤ cb.read ⟨n, hn⟩ ∧ cb.read ⟨n, hn⟩ ≤ '9' :=
begin
  have c9 : '9'.to_nat - '0'.to_nat = 9 := rfl,
  have l09 : '0'.to_nat ≤ '9'.to_nat := dec_trivial,
  have le_iff_le : ∀ {c c' : char}, c ≤ c' ↔ c.to_nat ≤ c'.to_nat := λ _ _, iff.rfl,
  split,
  { simp only [digit, sat_eq_done, pure_eq_done, decorate_error_eq_done, bind_eq_done, ←c9],
    rintro ⟨np, c, ⟨hn, ⟨ge0, le9⟩, rfl, rfl⟩, rfl, rfl⟩,
    simpa [hn, ge0, le9, true_and, and_true, eq_self_iff_true, exists_prop_of_true,
            nat.sub_le_sub_right_iff, l09] using (le_iff_le.mp le9) },
  { simp only [digit, sat_eq_done, pure_eq_done, decorate_error_eq_done, bind_eq_done, ←c9,
               le_iff_le],
    rintro ⟨hn, rfl, -, rfl, ge0, le9⟩,
    use [n + 1, cb.read ⟨n, hn⟩],
    simp [hn, ge0, le9] }
end

lemma digit_eq_fail : digit cb n = fail n' err ↔ n = n' ∧ err = dlist.of_list ["<digit>"] ∧
  ∀ (h : n < cb.size), ¬ ((λ c, '0' ≤ c ∧ c ≤ '9') (cb.read ⟨n, h⟩)) :=
by simp [digit, sat_eq_fail]


end done

namespace static

variables {α β : Type} {p q : parser α} {msgs : thunk (list string)} {msg : thunk string}
  {cb : char_buffer} {n' n : ℕ} {err : dlist string} {a : α} {b : β} {sep : parser unit}

lemma not_of_ne (h : p cb n = done n' a) (hne : n ≠ n') : ¬ static p :=
by { introI, exact hne (of_done h) }

instance pure : static (pure a) :=
⟨λ _ _ _ _, by { simp_rw pure_eq_done, rw [and.comm], simp }⟩

instance bind {f : α → parser β} [p.static] [∀ a, (f a).static] :
  (p >>= f).static :=
⟨λ _ _ _ _, by { rw bind_eq_done, rintro ⟨_, _, hp, hf⟩, exact trans (of_done hp) (of_done hf) }⟩

instance and_then {q : parser β} [p.static] [q.static] : (p >> q).static := static.bind

instance map [p.static] {f : α → β} : (f <$> p).static :=
⟨λ _ _ _ _, by { simp_rw map_eq_done, rintro ⟨_, hp, _⟩, exact of_done hp }⟩

instance seq {f : parser (α → β)} [f.static] [p.static] : (f <*> p).static := static.bind

instance mmap : Π {l : list α} {f : α → parser β}, (∀ a, (f a).static) → (l.mmap f).static
| []       _ _ := static.pure
| (a :: l) _ h := begin
  convert static.bind,
  { exact h _ },
  { intro,
    convert static.bind,
    { exact mmap h },
    { exact λ _, static.pure } }
end

instance mmap' : Π {l : list α} {f : α → parser β}, (∀ a, (f a).static) → (l.mmap' f).static
| []       _ _ := static.pure
| (a :: l) _ h := begin
  convert static.and_then,
  { exact h _ },
  { exact mmap' h }
end

instance failure : @parser.static α failure :=
⟨λ _ _ _ _, by simp⟩

instance guard {p : Prop} [decidable p] : static (guard p) :=
⟨λ _ _ _ _, by simp [guard_eq_done]⟩

instance orelse [p.static] [q.static] : (p <|> q).static :=
⟨λ _ _ _ _, by { simp_rw orelse_eq_done, rintro (h | ⟨h, -⟩); exact of_done h }⟩

instance decorate_errors [p.static] :
  (@decorate_errors α msgs p).static :=
⟨λ _ _ _ _, by { rw decorate_errors_eq_done, exact of_done }⟩

instance decorate_error [p.static] : (@decorate_error α msg p).static :=
static.decorate_errors

lemma any_char : ¬ static any_char :=
begin
  have : any_char "s".to_char_buffer 0 = done 1 's',
    { have : 0 < "s".to_char_buffer.size := dec_trivial,
      simpa [any_char_eq_done, this] },
  exact not_of_ne this zero_ne_one
end

lemma sat_iff {p : char → Prop} [decidable_pred p] : static (sat p) ↔ ∀ c, ¬ p c :=
begin
  split,
  { introI,
    intros c hc,
    have : sat p [c].to_buffer 0 = done 1 c := by simp [sat_eq_done, hc],
    exact zero_ne_one (of_done this) },
  { contrapose!,
    simp only [iff, sat_eq_done, and_imp, exists_prop, exists_and_distrib_right,
               exists_and_distrib_left, exists_imp_distrib, not_forall],
    rintros _ _ _ a h hne rfl hp -,
    exact ⟨a, hp⟩ }
end

instance sat : static (sat (λ _, false)) :=
by { apply sat_iff.mpr, simp }

instance eps : static eps := static.pure

lemma ch (c : char) : ¬ static (ch c) :=
begin
  have : ch c [c].to_buffer 0 = done 1 (),
    { have : 0 < [c].to_buffer.size := dec_trivial,
      simp [ch_eq_done, this] },
  exact not_of_ne this zero_ne_one
end

lemma char_buf_iff {cb' : char_buffer} : static (char_buf cb') ↔ cb' = buffer.nil :=
begin
  rw ←buffer.size_eq_zero_iff,
  have : char_buf cb' cb' 0 = done cb'.size () := by simp [char_buf_eq_done],
  cases hc : cb'.size with n,
  { simp only [eq_self_iff_true, iff_true],
    exact ⟨λ _ _ _ _ h, by simpa [hc] using (char_buf_eq_done.mp h).left⟩ },
  { rw hc at this,
    simpa [nat.succ_ne_zero] using not_of_ne this (nat.succ_ne_zero n).symm }
end

lemma one_of_iff {cs : list char} : static (one_of cs) ↔ cs = [] :=
begin
  cases cs with hd tl,
  { simp [one_of, static.decorate_errors] },
  { have : one_of (hd :: tl) (hd :: tl).to_buffer 0 = done 1 hd,
      { simp [one_of_eq_done] },
    simpa using not_of_ne this zero_ne_one }
end

instance one_of : static (one_of []) :=
by { apply one_of_iff.mpr, refl }

lemma one_of'_iff {cs : list char} : static (one_of' cs) ↔ cs = [] :=
begin
  cases cs with hd tl,
  { simp [one_of', static.bind], },
  { have : one_of' (hd :: tl) (hd :: tl).to_buffer 0 = done 1 (),
      { simp [one_of'_eq_done] },
    simpa using not_of_ne this zero_ne_one }
end

instance one_of' : static (one_of []) :=
by { apply one_of_iff.mpr, refl }

lemma str_iff {s : string} : static (str s) ↔ s = "" :=
by simp [str_eq_char_buf, char_buf_iff, ←string.to_list_inj, ←buffer.ext_iff]

instance remaining : remaining.static :=
⟨λ _ _ _ _ h, (remaining_eq_done.mp h).left⟩

instance eof : eof.static :=
static.decorate_error

instance foldr_core {f : α → β → β} [p.static] :
  ∀ {b : β} {reps : ℕ}, (foldr_core f p b reps).static
| _ 0          := static.failure
| _ (reps + 1) := begin
  simp_rw parser.foldr_core,
  convert static.orelse,
  { convert static.bind,
    { apply_instance },
    { intro,
      convert static.bind,
      { exact foldr_core },
      { apply_instance } } },
  { exact static.pure }
end

instance foldr {f : α → β → β} [p.static] : static (foldr f p b) :=
⟨λ _ _ _ _, by { dsimp [foldr], exact of_done }⟩

instance foldl_core {f : α → β → α} {p : parser β} [p.static] :
  ∀ {a : α} {reps : ℕ}, (foldl_core f a p reps).static
| _ 0          := static.failure
| _ (reps + 1) := begin
  convert static.orelse,
  { convert static.bind,
    { apply_instance },
    { exact λ _, foldl_core } },
  { exact static.pure }
end

instance foldl {f : α → β → α} {p : parser β} [p.static] : static (foldl f a p) :=
⟨λ _ _ _ _, by { dsimp [foldl], exact of_done }⟩

instance many [p.static] : p.many.static :=
static.foldr

instance many_char {p : parser char} [p.static] : p.many_char.static :=
static.map

instance many' [p.static] : p.many'.static :=
static.and_then

instance many1 [p.static] : p.many1.static :=
static.seq

instance many_char1 {p : parser char} [p.static] : p.many_char1.static :=
static.map

instance sep_by1 [p.static] [sep.static] : static (sep_by1 sep p) :=
static.seq

instance sep_by [p.static] [sep.static] : static (sep_by sep p) :=
static.orelse

lemma fix_core {F : parser α → parser α} (hF : ∀ (p : parser α), p.static → (F p).static) :
  ∀ (max_depth : ℕ), static (fix_core F max_depth)
| 0               := static.failure
| (max_depth + 1) := hF _ (fix_core _)

lemma digit : ¬ digit.static :=
begin
  have : digit "1".to_char_buffer 0 = done 1 1,
    { have : 0 < "s".to_char_buffer.size := dec_trivial,
      simpa [this] },
  exact not_of_ne this zero_ne_one
end

lemma nat : ¬ nat.static :=
begin
  have : nat "1".to_char_buffer 0 = done 1 1,
    { have : 0 < "s".to_char_buffer.size := dec_trivial,
      simpa [this] },
  exact not_of_ne this zero_ne_one
end

lemma fix {F : parser α → parser α} (hF : ∀ (p : parser α), p.static → (F p).static) :
  static (fix F) :=
⟨λ cb n _ _ h,
  by { haveI := fix_core hF (cb.size - n + 1), dsimp [fix] at h, exact static.of_done h }⟩

end static

namespace bounded

variables {α β : Type} {msgs : thunk (list string)} {msg : thunk string}
variables {p q : parser α} {cb : char_buffer} {n n' : ℕ} {err : dlist string}
variables {a : α} {b : β}

lemma done_of_unbounded (h : ¬p.bounded) : ∃ (cb : char_buffer) (n n' : ℕ) (a : α),
  p cb n = done n' a ∧ cb.size ≤ n :=
begin
  contrapose! h,
  constructor,
  intros cb n hn,
  cases hp : p cb n,
  { exact absurd hn (h _ _ _ _ hp).not_le },
  { simp [hp] }
end

lemma pure : ¬ bounded (pure a) :=
begin
  introI,
  have : (pure a : parser α) buffer.nil 0 = done 0 a := by simp [pure_eq_done],
  exact absurd (bounded.of_done this) (lt_irrefl _)
end

instance bind {f : α → parser β} [p.bounded] :
  (p >>= f).bounded :=
begin
  constructor,
  intros cb n hn,
  obtain ⟨_, _, hp⟩ := bounded.exists p hn,
  simp [hp]
end

instance and_then {q : parser β} [p.bounded] : (p >> q).bounded :=
bounded.bind

instance map [p.bounded] {f : α → β} : (f <$> p).bounded :=
bounded.bind

instance seq {f : parser (α → β)} [f.bounded] : (f <*> p).bounded :=
bounded.bind

instance mmap {a : α} {l : list α} {f : α → parser β} [∀ a, (f a).bounded] :
  ((a :: l).mmap f).bounded :=
bounded.bind

instance mmap' {a : α} {l : list α} {f : α → parser β} [∀ a, (f a).bounded] :
  ((a :: l).mmap' f).bounded :=
bounded.and_then

instance failure : @parser.bounded α failure :=
⟨by simp⟩

lemma guard_iff {p : Prop} [decidable p] : bounded (guard p) ↔ ¬ p :=
by simpa [guard, apply_ite bounded, pure, failure] using λ _, bounded.failure

instance orelse [p.bounded] [q.bounded] : (p <|> q).bounded :=
begin
  constructor,
  intros cb n hn,
  cases hx : (p <|> q) cb n with posx resx posx errx,
  { obtain h | ⟨h, -, -⟩ := orelse_eq_done.mp hx;
    exact absurd hn (of_done h).not_le },
  { simp }
end

instance decorate_errors [p.bounded] :
  (@decorate_errors α msgs p).bounded :=
begin
  constructor,
  intros _ _,
  simpa using bounded.exists p
end

lemma decorate_errors_iff : (@parser.decorate_errors α msgs p).bounded ↔ p.bounded :=
begin
  split,
  { introI,
    constructor,
    intros _ _ hn,
    obtain ⟨_, _, h⟩ := bounded.exists (@parser.decorate_errors α msgs p) hn,
    simp [decorate_errors_eq_fail] at h,
    exact h.right.right },
  { introI,
    constructor,
    intros _ _ hn,
    obtain ⟨_, _, h⟩ := bounded.exists p hn,
    simp [h] }
end

instance decorate_error [p.bounded] : (@decorate_error α msg p).bounded :=
bounded.decorate_errors

lemma decorate_error_iff : (@parser.decorate_error α msg p).bounded ↔ p.bounded :=
decorate_errors_iff

instance any_char : bounded any_char :=
⟨λ cb n hn, by simp [any_char, hn]⟩

instance sat {p : char → Prop} [decidable_pred p] : bounded (sat p) :=
⟨λ cb n hn, by simp [sat, hn]⟩

lemma eps : ¬ bounded eps := pure

instance ch {c : char} : bounded (ch c) :=
bounded.decorate_error

lemma char_buf_iff {s : char_buffer} : bounded (char_buf s) ↔ s.to_list ≠ [] :=
begin
  rw [char_buf, decorate_error_iff],
  cases s.to_list,
  { simp [pure, ch] },
  { simp only [iff_true, ne.def, not_false_iff],
    apply_instance }
end

instance one_of {cs : list char} : (one_of cs).bounded :=
bounded.decorate_errors

instance one_of' {cs : list char} : (one_of' cs).bounded :=
bounded.and_then

lemma str_iff {s : string} : (str s).bounded ↔ s ≠ "" :=
begin
  rw [str, decorate_error_iff],
  cases hs : s.to_list,
  { have : s = "",
      { cases s, rw [string.to_list] at hs, simpa [hs] },
    simp [pure, this] },
  { have : s ≠ "",
      { intro H, simpa [H] using hs },
    simp only [this, iff_true, ne.def, not_false_iff],
    apply_instance }
end

lemma remaining : ¬ remaining.bounded :=
begin
  introI,
  have : remaining buffer.nil 0 = done 0 0 := by simp [remaining_eq_done],
  exact absurd (bounded.of_done this) (lt_irrefl _)
end

lemma eof : ¬ eof.bounded :=
begin
  introI,
  have : eof buffer.nil 0 = done 0 () := by simp [eof_eq_done],
  exact absurd (bounded.of_done this) (lt_irrefl _)
end

section fold

instance foldr_core_zero {f : α → β → β} : (foldr_core f p b 0).bounded :=
bounded.failure

instance foldl_core_zero {f : β → α → β} {b : β} : (foldl_core f b p 0).bounded :=
bounded.failure

variables {reps : ℕ} [hpb : p.bounded] (he : ∀ cb n n' err, p cb n = fail n' err → n ≠ n')
include hpb he

lemma foldr_core {f : α → β → β} : (foldr_core f p b reps).bounded :=
begin
  cases reps,
  { exact bounded.foldr_core_zero },
  constructor,
  intros cb n hn,
  obtain ⟨np, errp, hp⟩ := bounded.exists p hn,
  simpa [foldr_core_succ_eq_fail, hp] using he cb n np errp,
end

lemma foldr {f : α → β → β} : bounded (foldr f p b) :=
begin
  constructor,
  intros cb n hn,
  haveI : (parser.foldr_core f p b (cb.size - n + 1)).bounded := foldr_core he,
  obtain ⟨np, errp, hp⟩ := bounded.exists (parser.foldr_core f p b (cb.size - n + 1)) hn,
  simp [foldr, hp]
end

lemma foldl_core {f : β → α → β} :
  (foldl_core f b p reps).bounded :=
begin
  cases reps,
  { exact bounded.foldl_core_zero },
  constructor,
  intros cb n hn,
  obtain ⟨np, errp, hp⟩ := bounded.exists p hn,
  simpa [foldl_core_succ_eq_fail, hp] using he cb n np errp,
end

lemma foldl {f : β → α → β} : bounded (foldl f b p) :=
begin
  constructor,
  intros cb n hn,
  haveI : (parser.foldl_core f b p (cb.size - n + 1)).bounded := foldl_core he,
  obtain ⟨np, errp, hp⟩ := bounded.exists (parser.foldl_core f b p (cb.size - n + 1)) hn,
  simp [foldl, hp]
end

lemma many : p.many.bounded :=
foldr he

lemma many_char {pc : parser char} [pc.bounded]
  (he : ∀ cb n n' err, pc cb n = fail n' err → n ≠ n'): pc.many_char.bounded :=
by { convert bounded.map, exact many he }

lemma many' : p.many'.bounded :=
by { convert bounded.and_then, exact many he }

end fold

instance many1 [p.bounded] : p.many1.bounded :=
bounded.seq

instance many_char1 {p : parser char} [p.bounded] : p.many_char1.bounded :=
bounded.map

instance sep_by1 {sep : parser unit} [p.bounded] : bounded (sep_by1 sep p) :=
bounded.seq

lemma fix_core {F : parser α → parser α} (hF : ∀ (p : parser α), p.bounded → (F p).bounded) :
  ∀ (max_depth : ℕ), bounded (fix_core F max_depth)
| 0               := bounded.failure
| (max_depth + 1) := hF _ (fix_core _)

instance digit : digit.bounded :=
bounded.decorate_error

instance nat : nat.bounded :=
bounded.decorate_error

lemma fix {F : parser α → parser α} (hF : ∀ (p : parser α), p.bounded → (F p).bounded) :
  bounded (fix F) :=
begin
  constructor,
  intros cb n hn,
  haveI : (parser.fix_core F (cb.size - n + 1)).bounded := fix_core hF _,
  obtain ⟨np, errp, hp⟩ := bounded.exists (parser.fix_core F (cb.size - n + 1)) hn,
  simp [fix, hp]
end

end bounded

variables {α β : Type} {msgs : thunk (list string)} {msg : thunk string}
variables {p q : parser α} {cb : char_buffer} {n n' : ℕ} {err : dlist string}
variables {a : α} {b : β}

lemma nat_eq_done {k : ℕ} (h : nat cb n = done n' k) :
  k = (nat.of_digits 10 (((cb.to_list.drop n).take (n' - n)).map (λ c, c.to_nat - '0'.to_nat)))
  -- ∧ ∃ (h : n' < cb.size), ¬ ((λ c, '0' ≤ c ∧ c ≤ '9') (cb.read ⟨n', h⟩))
    :=
begin
  -- split,
  -- { intro h,
  have := bounded.of_done h,
  have natm : nat._match_1 = (λ (d : ℕ) p, ⟨p.1 + d * p.2, p.2 * 10⟩),
    { ext1, ext1 ⟨⟩, refl },
  have : ∀ l, list.foldr (λ (x y : ℕ), 10 * y) 1 l = (list.foldr nat._match_1 (0, 1) l).snd,
    { intro l,
      rw natm,
      induction l with hd tl hl,
      { simp },
      { simp only [hl, list.foldr],
        rw mul_comm } },
  have : ∀ l, list.foldr (λ (x y : ℕ), x + 10 * y) 0 l = (list.foldr nat._match_1 (0, 1) l).fst,
    { intro l,
      rw natm,
      induction l with hd tl hl,
      { simp },
      { rw list.foldr,
        rw list.foldr,
        rw ←natm,
        rw ←this,
        rw natm,
        rw ←hl,
        simp,
      },
    },
  rw nat at h,
  simp [nat, pure_eq_done, and.comm, and.left_comm, and.assoc, this] at h,
  rcases h with ⟨l, hl, rfl⟩,
  rw [nat.of_digits_eq_foldr],
  cases l,
  { simpa using hl },
  { simp, },
  -- change (∃ (x : list ℕ), _ ∧ prod.fst (list.foldr (λ d p, _) (0, 1) x) = k) at h,
  -- rw ←buffer.to_buffer_to_list cb at *,
  -- simp,
  -- induction hc : cb.to_list with chd ctl hl,
  -- { simp at this,
  --   simp,
  -- },
  -- { have : n ≤ n' := sorry, },
  -- {  },
  -- simp [nat.of_digits_eq_foldr],
  -- },
  -- {  },
  -- induction hn : n' - n with m hm,
  -- { simp [nat.of_digits_eq_foldr, nat, pure_eq_done, and.left_comm],
  --   split,
  --   { rintro ⟨l, h, rfl⟩,
  --     have : n' = n := le_antisymm (nat.le_of_sub_eq_zero hn) (mono.of_done h),
  --     subst this,
  --     rcases l with (_ | ⟨hd, _ | ⟨hd', tl⟩⟩),
  --     { simp },
  --     { simpa only [many1_eq_done, digit_eq_done, and.left_comm, many_eq_done_nil, exists_eq_left,
  --                   exists_and_distrib_left, self_eq_add_right, one_ne_zero, false_and] using h },
  --     { simp [many1_eq_done, digit_eq_done, and.left_comm, and.comm, and.assoc, many_eq_done] at h,
  --       rcases h with ⟨lhd, lhd', h, ⟨hlt, ge0, le9, rfl⟩, ⟨hlt', ge0', le9', rfl⟩⟩,
  --       simp [hlt, ge0, le9.not_lt],
  --       -- obtain ⟨r, hr⟩ : ∃ r, n' + 1 + r = cb.size := nat.le.dest hlt,
  --       -- cases r,
  --       -- { simpa [←hr, lt_irrefl] using hlt' },
  --       -- { replace hr : r + 1 = cb.size - (n' + 1),
  --       --     { rw [nat.sub_eq_of_eq_add],
  --       --       simp [←hr] },
  --       --   simp [←hr, foldr_core_eq_done, digit_eq_done, and.comm, and.left_comm, and.assoc] at h,
  --       --   simp,
  --       -- },
  --     },
  --   },
  --   {  },
  -- },
  -- {  },
end

#exit

namespace unfailing

variables {α β : Type} {p q : parser α} {msgs : thunk (list string)} {msg : thunk string}
  {cb : char_buffer} {n' n : ℕ} {err : dlist string} {a : α} {b : β} {sep : parser unit}

instance pure : unfailing (pure a) :=
⟨λ _ _, by simp [pure_eq_done]⟩

instance bind {f : α → parser β} [p.unfailing] [∀ a, (f a).unfailing] :
  (p >>= f).unfailing :=
⟨λ cb n, begin
  obtain ⟨np, a, hp⟩ := exists_done p cb n,
  simpa [hp, and.comm, and.left_comm, and.assoc] using exists_done (f a) cb np
end⟩

instance and_then {q : parser β} [p.unfailing] [q.unfailing] : (p >> q).unfailing := unfailing.bind

instance map [p.unfailing] {f : α → β} : (f <$> p).unfailing := unfailing.bind

instance seq {f : parser (α → β)} [f.unfailing] [p.unfailing] : (f <*> p).unfailing :=
unfailing.bind

instance mmap {l : list α} {f : α → parser β} [∀ a, (f a).unfailing] : (l.mmap f).unfailing :=
begin
  constructor,
  induction l with hd tl hl,
  { intros,
    simp [pure_eq_done] },
  { intros,
    obtain ⟨np, a, hp⟩ := exists_done (f hd) cb n,
    obtain ⟨n', b, hf⟩ := hl cb np,
    simp [hp, hf, and.comm, and.left_comm, and.assoc, pure_eq_done] }
end

instance mmap' {l : list α} {f : α → parser β} [∀ a, (f a).unfailing] : (l.mmap' f).unfailing :=
begin
  constructor,
  induction l with hd tl hl,
  { intros,
    simp [pure_eq_done] },
  { intros,
    obtain ⟨np, a, hp⟩ := exists_done (f hd) cb n,
    obtain ⟨n', b, hf⟩ := hl cb np,
    simp [hp, hf, and.comm, and.left_comm, and.assoc, pure_eq_done] }
end

lemma failure : ¬ @parser.unfailing α failure :=
begin
  introI h,
  have : (failure : parser α) ("".to_char_buffer) 0 = fail 0 dlist.empty := by simp,
  exact of_fail this
end

instance guard_true : unfailing (guard true) := unfailing.pure

lemma guard : ¬ unfailing (guard false) :=
unfailing.failure

instance orelse [p.unfailing] : (p <|> q).unfailing :=
⟨λ cb n, by { obtain ⟨_, _, h⟩ := p.exists_done cb n, simp [success_iff, h] }⟩

instance decorate_errors [p.unfailing] :
  (@decorate_errors α msgs p).unfailing :=
⟨λ cb n, by { obtain ⟨_, _, h⟩ := p.exists_done cb n, simp [success_iff, h] }⟩

instance decorate_error [p.unfailing] : (@decorate_error α msg p).unfailing :=
unfailing.decorate_errors

instance any_char : conditionally_unfailing any_char :=
⟨λ _ _ hn, by simp [success_iff, any_char_eq_done, hn]⟩

lemma sat : conditionally_unfailing (sat (λ _, true)) :=
⟨λ _ _ hn, by simp [success_iff, sat_eq_done, hn]⟩

instance eps : unfailing eps := unfailing.pure

instance remaining : remaining.unfailing :=
⟨λ _ _, by simp [success_iff, remaining_eq_done]⟩

lemma foldr_core_zero {f : α → β → β} {b : β} : ¬ (foldr_core f p b 0).unfailing :=
unfailing.failure

instance foldr_core_of_static {f : α → β → β} {b : β} {reps : ℕ} [p.static] [p.unfailing] :
  (foldr_core f p b (reps + 1)).unfailing :=
begin
  induction reps with reps hr,
  { constructor,
    intros cb n,
    obtain ⟨np, a, h⟩ := p.exists_done cb n,
    simpa [foldr_core_eq_done, h] using (static.of_done h).symm },
  { constructor,
    haveI := hr,
    intros cb n,
    obtain ⟨np, a, h⟩ := p.exists_done cb n,
    have : n = np := static.of_done h,
    subst this,
    obtain ⟨np, b', hf⟩ := exists_done (foldr_core f p b (reps + 1)) cb n,
    have : n = np := static.of_done hf,
    subst this,
    refine ⟨n, f a b', _⟩,
    rw foldr_core_eq_done,
    simp [h, hf, and.comm, and.left_comm, and.assoc] }
end

instance foldr_core_one_of_err_static {f : α → β → β} {b : β} {reps : ℕ} [p.static] [p.err_static] :
  (foldr_core f p b 1).unfailing :=
begin
  constructor,
  intros cb n,
  cases h : p cb n,
  { simpa [foldr_core_eq_done, h] using (static.of_done h).symm },
  { simpa [foldr_core_eq_done, h] using (err_static.of_fail h).symm }
end

instance [has_repr α] : has_repr (parse_result α) :=
⟨ λ x, match x with
  | done n a := sformat!"done with {repr a} at {n}"
  | fail n err := sformat!"fail with {err.to_list} at {n}"
  end
⟩

#eval parser.foldr list.cons
  (decorate_error "" $ prod.mk <$> decorate_error ("") any_char <*> any_char)
  [] "abcdef".to_char_buffer 1

#eval nat "12345a".to_char_buffer 0


-- instance foldr_core {f : α → β → β} {b : β} {reps : ℕ} [p.err_static] :
--   (foldr_core f p b (reps + 2)).unfailing :=
-- begin
--   induction reps with reps hr,
--   { constructor,
--     intros cb n,
--     cases hp : p cb n with np a np errp,
--     { cases hf : foldr_core f p b 1 cb np with n' b' n' errf,
--       { have := hf,
--         simp only [foldr_core_eq_done, foldr_core_zero_eq_done, foldr_core_zero_eq_fail, false_or,
--                     exists_and_distrib_right, exists_false, and_false, false_and] at this,
--         rcases this with ⟨rfl, rfl, err', hp' | ⟨n', ⟨a', hp'⟩, rfl, rfl⟩⟩,
--         { simp [foldr_core_eq_done, hp, hp', hf, and.comm, and.left_comm, and.assoc] },
--         { simp [foldr_core_eq_done, hp, hp', hf, and.comm, and.left_comm, and.assoc] } },
--       { have := hf,
--         simp only [foldr_core_succ_eq_fail, foldr_core_zero_eq_fail, ne.def, and.comm, and.left_comm,
--                   exists_eq_left, exists_and_distrib_left] at this,
--         rcases this with ⟨hn, hp' | ⟨rfl, a', hp'⟩⟩,
--         { exact absurd (err_static.of_fail hp') hn },
--         { simp [foldr_core_eq_done, hp, hp', hf, and.comm, and.left_comm, and.assoc, ne.symm hn], },
--       },
--     }

    -- obtain ⟨np, a, h⟩ := p.exists_done cb n,
    -- obtain ⟨np', a', h'⟩ := p.exists_done cb np,
    -- simp [foldr_core],
    -- cases hf : (foldr_core f p b 1) cb np',
    -- { have := hf,
    --   simp [foldr_core_eq_done, h', foldr_core_zero_eq_done, foldr_core_zero_eq_fail, false_or,
    --              exists_and_distrib_right, exists_false, exists_eq_right, exists_eq_right',
    --              exists_eq_left', and_false, false_and] at this,
    --   rcases this with ⟨rfl, rfl, rfl⟩,
    --   simp [foldr_core_eq_done, h, h', hf, and.comm, and.left_comm, and.assoc] },
    -- { have := hf,
    --   simp [foldr_core_succ_eq_fail, h'] at this,
    --   simp [foldr_core_eq_done, hf, h', h, and.comm, and.left_comm, and.assoc],
    -- },
    -- -- obtain ⟨n', b, hf⟩ := (foldr_core f p b 1).exists_done cb np',
    -- simp [foldr_core_eq_done, h, h', and.comm, and.left_comm, and.assoc],
    -- -- obtain ⟨np', a', h'⟩ := p.exists_done cb np,
    -- -- rintro _ _ H,
    -- -- rw foldr_core_succ_eq_fail at H,
    -- -- rintro _ _ hne hne' rfl rfl,
--   },
--   {  },
-- end

instance foldr {f : α → β → β} [p.bounded] [p.prog] [p.unfailing] : unfailing (foldr f p b) :=
begin
  constructor,
  intros cb n,
  simp [foldr_eq_done],
  obtain ⟨np, a, h⟩ := p.exists_done cb n,
  obtain ⟨k, hk⟩ := nat.exists_eq_add_of_lt (bounded.of_done h),
  have : cb.size - n = k + 1,
    { rw [hk, add_assoc, nat.add_sub_cancel_left] },
  simp_rw [foldr, this, foldr_core_succ_eq_fail],
  rintro ⟨hne, H | ⟨np, a, hp, hne', H | ⟨np', a', H, hf⟩⟩⟩,
  { exact false.elim (of_fail H) },
  { exact false.elim (of_fail H) },
  {
    induction k with k IH,
    {  },
    {  },
  },

  -- cases k,
  -- { simp [hk, foldr_core_succ_eq_fail, h],
  --   rintros hnp (H | ⟨np', ⟨a', H⟩, rfl, rfl⟩),
  --   { replace hk : n = cb.size - 1 := by simp [hk],
  --     subst hk,
  --     have : cb.size ≤ np := nat.le_of_pred_lt (prog.of_done h),
  --     exact absurd this (not_le_of_lt (bounded.of_done H)) } },
  -- { have : n + k.succ + 1 - n = k + 2,
  --     { rw [add_assoc, nat.add_sub_cancel_left] },
  --   simp [hk, this, foldr_core_succ_eq_fail, h, and.comm, and.assoc, and.left_comm],
  --   rintros hnp hnp' (H | ⟨np', hnp'', ⟨a, H⟩, H'⟩),
  --   { exact false.elim (of_fail H) },
  --   {  },
  --   },
  -- -- rcases hk : cb.size - n with _|_|k,
  -- -- { exact absurd (nat.le_of_sub_eq_zero hk) (not_le_of_lt (bounded.of_done h)) },
  -- -- { simp [h, foldr_eq_fail, foldr_core_succ_eq_fail, hk],
  -- --   rintros hnp (H | ⟨np', ⟨a', H⟩, rfl, rfl⟩),
  -- --   { exact false.elim (of_fail H) },
  -- --   {
  -- --     have : n = cb.size - 1,
  -- --       { rw nat.sub, },
  -- --   } },
  -- -- { sorry } ,
end

instance foldl_core {f : α → β → α} {p : parser β} [p.unfailing] :
  ∀ {a : α} {reps : ℕ}, (foldl_core f a p reps).unfailing
| _ 0          := unfailing.failure
| _ (reps + 1) := begin
  convert unfailing.orelse,
  { convert unfailing.bind,
    { apply_instance },
    { exact λ _, foldl_core } },
  { exact unfailing.pure }
end

instance foldl {f : α → β → α} {p : parser β} [p.unfailing] : unfailing (foldl f a p) :=
⟨λ _ _, unfailing.foldl_core.le _ _⟩

instance many [p.unfailing] : p.many.unfailing :=
unfailing.foldr

instance many_char {p : parser char} [p.unfailing] : p.many_char.unfailing :=
unfailing.map

instance many' [p.unfailing] : p.many'.unfailing :=
unfailing.and_then

instance many1 [p.unfailing] : p.many1.unfailing :=
unfailing.seq

instance many_char1 {p : parser char} [p.unfailing] : p.many_char1.unfailing :=
unfailing.map

instance sep_by1 [p.unfailing] [sep.unfailing] : unfailing (sep_by1 sep p) :=
unfailing.seq

instance sep_by [p.unfailing] [sep.unfailing] : unfailing (sep_by sep p) :=
unfailing.orelse

lemma fix_core {F : parser α → parser α} (hF : ∀ (p : parser α), p.unfailing → (F p).unfailing) :
  ∀ (max_depth : ℕ), unfailing (fix_core F max_depth)
| 0               := unfailing.failure
| (max_depth + 1) := hF _ (fix_core _)

instance digit : digit.unfailing :=
unfailing.decorate_error

instance nat : nat.unfailing :=
unfailing.decorate_error

lemma fix {F : parser α → parser α} (hF : ∀ (p : parser α), p.unfailing → (F p).unfailing) :
  unfailing (fix F) :=
⟨λ _ _, by { convert unfailing.fix_core.le _ _, exact hF }⟩

end unfailing

namespace err_static

variables {α β : Type} {p q : parser α} {msgs : thunk (list string)} {msg : thunk string}
  {cb : char_buffer} {n' n : ℕ} {err : dlist string} {a : α} {b : β} {sep : parser unit}

lemma not_of_ne (h : p cb n = fail n' err) (hne : n ≠ n') : ¬ err_static p :=
by { introI, exact hne (of_fail h) }

instance pure : err_static (pure a) :=
⟨λ _ _ _ _, by { simp [pure_eq_done] }⟩

instance bind {f : α → parser β} [p.static] [p.err_static] [∀ a, (f a).err_static] :
  (p >>= f).err_static :=
⟨λ cb n n' err, begin
  rw bind_eq_fail,
  rintro (hp | ⟨_, _, hp, hf⟩),
  { exact of_fail hp },
  { exact trans (static.of_done hp) (of_fail hf) }
end⟩

instance bind_of_unfailing {f : α → parser β} [p.err_static] [∀ a, (f a).unfailing] :
  (p >>= f).err_static :=
⟨λ cb n n' err, begin
  rw bind_eq_fail,
  rintro (hp | ⟨_, _, hp, hf⟩),
  { exact of_fail hp },
  { exact false.elim (unfailing.of_fail hf) }
end⟩

instance and_then {q : parser β} [p.static] [p.err_static] [q.err_static] : (p >> q).err_static :=
err_static.bind

instance and_then_of_unfailing {q : parser β} [p.err_static] [q.unfailing] : (p >> q).err_static :=
err_static.bind_of_unfailing

instance map [p.err_static] {f : α → β} : (f <$> p).err_static :=
⟨λ _ _ _ _, by { rw map_eq_fail, exact of_fail }⟩

instance seq {f : parser (α → β)} [f.static] [f.err_static] [p.err_static] : (f <*> p).err_static :=
err_static.bind

instance seq_of_unfailing {f : parser (α → β)} [f.err_static] [p.unfailing] :
  (f <*> p).err_static :=
err_static.bind_of_unfailing

instance mmap : Π {l : list α} {f : α → parser β},
  (∀ a, (f a).static) → (∀ a, (f a).err_static) → (l.mmap f).err_static
| []       _ _ _  := err_static.pure
| (a :: l) _ h h' := begin
  convert err_static.bind,
  { exact h _ },
  { exact h' _ },
  { intro,
    convert err_static.bind,
    { exact static.mmap h },
    { exact mmap h h' },
    { exact λ _, err_static.pure } }
end

instance mmap_of_unfailing : Π {l : list α} {f : α → parser β},
  (∀ a, (f a).unfailing) → (∀ a, (f a).err_static) → (l.mmap f).err_static
| []       _ _ _  := err_static.pure
| (a :: l) _ h h' := begin
  convert err_static.bind_of_unfailing,
  { exact h' _ },
  { intro,
    convert unfailing.bind,
    { convert unfailing.mmap,
      exact h },
    { exact λ _, unfailing.pure } }
end

instance mmap' : Π {l : list α} {f : α → parser β},
  (∀ a, (f a).static) → (∀ a, (f a).err_static) → (l.mmap' f).err_static
| []       _ _ _  := err_static.pure
| (a :: l) _ h h' := begin
  convert err_static.and_then,
  { exact h _ },
  { exact h' _ },
  { exact mmap' h h' }
end

instance mmap'_of_unfailing : Π {l : list α} {f : α → parser β},
  (∀ a, (f a).unfailing) → (∀ a, (f a).err_static) → (l.mmap' f).err_static
| []       _ _ _  := err_static.pure
| (a :: l) _ h h' := begin
  convert err_static.and_then_of_unfailing,
  { exact h' _ },
  { convert unfailing.mmap',
    exact h }
end

instance failure : @parser.err_static α failure :=
⟨λ _ _ _ _ h, (failure_eq_fail.mp h).left⟩

instance guard {p : Prop} [decidable p] : err_static (guard p) :=
⟨λ _ _ _ _ h, (guard_eq_fail.mp h).right.left⟩

instance orelse [p.err_static] [q.mono] : (p <|> q).err_static :=
⟨λ _ n n' _, begin
  by_cases hn : n = n',
  { exact λ _, hn },
  { rw orelse_eq_fail_of_mono_ne hn,
    { exact of_fail },
    { apply_instance } }
end⟩

instance decorate_errors :
  (@decorate_errors α msgs p).err_static :=
⟨λ _ _ _ _ h, (decorate_errors_eq_fail.mp h).left⟩

instance decorate_error : (@decorate_error α msg p).err_static :=
err_static.decorate_errors

instance any_char : err_static any_char :=
⟨λ _ _ _ _, by { rw [any_char_eq_fail, and.comm], simp }⟩

instance sat_iff {p : char → Prop} [decidable_pred p] : err_static (sat p) :=
⟨λ _ _ _ _ h, (sat_eq_fail.mp h).left⟩

instance eps : err_static eps := err_static.pure

instance ch (c : char) : err_static (ch c) :=
err_static.decorate_error

instance char_buf {cb' : char_buffer} : err_static (char_buf cb') :=
err_static.decorate_error

instance one_of {cs : list char} : err_static (one_of cs) :=
err_static.decorate_errors

instance one_of' {cs : list char} : err_static (one_of' cs) :=
err_static.and_then_of_unfailing

instance str {s : string} : err_static (str s) :=
err_static.decorate_error

instance remaining : remaining.err_static :=
⟨λ _ _ _ _, by simp [remaining_ne_fail]⟩

instance eof : eof.err_static :=
err_static.decorate_error

-- lemma foldr_core_err_static_unfailing {f : α → β → β} [p.err_static] :
--   ∀ {b : β} {reps : ℕ}, (foldr_core f p b reps).err_static ∧ (foldr_core f p b reps).unfailing
-- -- | _ 0          := ⟨err_static.failure, _⟩

-- instance foldr_core {f : α → β → β} [p.err_static] :
--   ∀ {b : β} {reps : ℕ}, (foldr_core f p b reps).err_static
-- | _ 0          := err_static.failure
-- | _ 1          := begin
--   simp_rw parser.foldr_core,
--   constructor,
--   simp,
--   rintros,
-- end
-- | _ (reps + 2) := begin
--   simp_rw parser.foldr_core,
--   convert err_static.orelse,
--   { convert err_static.bind_of_unfailing,
--     { apply_instance },
--     { intro,
--       convert unfailing.bind,
--       { sorry },
--       { apply_instance } } },
--   { apply_instance }
-- end

instance foldr {f : α → β → β} [p.err_static] : err_static (foldr f p b) :=
-- ⟨λ _ _ _ _, by { dsimp [foldr], exact of_done }⟩
begin
  constructor,
  intros cb n n' err,
  rw [foldr_eq_fail],
  rintro ⟨hn, hp | ⟨np, a, hp, hf⟩⟩,
  { exact of_fail hp },
  { cases hc : cb.size - n,
    {  },
    {  },
  },
  intro,
end

instance foldl_core {f : α → β → α} {p : parser β} [p.err_static] :
  ∀ {a : α} {reps : ℕ}, (foldl_core f a p reps).err_static
| _ 0          := err_static.failure
| _ (reps + 1) := begin
  convert err_static.orelse,
  { convert err_static.bind,
    { apply_instance },
    { exact λ _, foldl_core } },
  { exact err_static.pure }
end

instance foldl {f : α → β → α} {p : parser β} [p.err_static] : err_static (foldl f a p) :=
⟨λ _ _ _ _, by { dsimp [foldl], exact of_done }⟩

instance many [p.err_static] : p.many.err_static :=
err_static.foldr

instance many_char {p : parser char} [p.err_static] : p.many_char.err_static :=
err_static.map

instance many' [p.err_static] : p.many'.err_static :=
err_static.and_then

instance many1 [p.err_static] : p.many1.err_static :=
err_static.seq

instance many_char1 {p : parser char} [p.err_static] : p.many_char1.err_static :=
err_static.map

instance sep_by1 [p.err_static] [sep.err_static] : err_static (sep_by1 sep p) :=
err_static.seq

instance sep_by [p.err_static] [sep.err_static] : err_static (sep_by sep p) :=
err_static.orelse

lemma fix_core {F : parser α → parser α} (hF : ∀ (p : parser α), p.err_static → (F p).err_static) :
  ∀ (max_depth : ℕ), err_static (fix_core F max_depth)
| 0               := err_static.failure
| (max_depth + 1) := hF _ (fix_core _)

lemma digit : ¬ digit.err_static :=
begin
  have : digit "1".to_char_buffer 0 = done 1 1,
    { have : 0 < "s".to_char_buffer.size := dec_trivial,
      simpa [this] },
  exact not_of_ne this zero_ne_one
end

lemma nat : ¬ nat.err_static :=
begin
  have : nat "1".to_char_buffer 0 = done 1 1,
    { have : 0 < "s".to_char_buffer.size := dec_trivial,
      simpa [this] },
  exact not_of_ne this zero_ne_one
end

lemma fix {F : parser α → parser α} (hF : ∀ (p : parser α), p.err_static → (F p).err_static) :
  err_static (fix F) :=
⟨λ cb n _ _ h,
  by { haveI := fix_core hF (cb.size - n + 1), dsimp [fix] at h, exact err_static.of_done h }⟩

example : (prod.mk <$> any_char <*> any_char).unfailing :=
begin
  convert unfailing.seq,
  { convert unfailing.map,
    apply_instance
  },
end

end err_static

#exit

namespace prog

variables {α β : Type} {p q : parser α} {msgs : thunk (list string)} {msg : thunk string}
  {cb : char_buffer} {n' n : ℕ} {err : dlist string} {a : α} {b : β} {sep : parser unit}

lemma pure (a : α) : ¬ prog (pure a) :=
begin
  introI h,
  have : (pure a : parser α) (string.to_char_buffer "") 0 = done 0 a := by simp [pure_eq_done],
  replace this : 0 < 0 := prog.of_done this,
  exact (lt_irrefl _) this
end

instance bind {f : α → parser β} [p.prog] [∀ a, (f a).mono] :
  (p >>= f).prog :=
⟨λ _ _ _ _, by { simp_rw bind_eq_done, rintro ⟨_, _, hp, hf⟩,
  exact lt_of_lt_of_le (of_done hp) (mono.of_done hf) }⟩

instance and_then {q : parser β} [p.prog] [q.mono] : (p >> q).prog := prog.bind

instance map [p.prog] {f : α → β} : (f <$> p).prog :=
⟨λ _ _ _ _, by { simp_rw map_eq_done, rintro ⟨_, hp, _⟩, exact of_done hp }⟩

instance seq {f : parser (α → β)} [f.prog] [p.mono] : (f <*> p).prog := prog.bind

instance mmap {l : list α} {f : α → parser β} [(f a).prog] [∀ a, (f a).mono] :
  ((a :: l).mmap f).prog :=
begin
  constructor,
  simp only [and_imp, bind_eq_done, return_eq_pure, mmap, exists_imp_distrib, pure_eq_done],
  rintro _ _ _ _ _ _ h _ _ hp rfl rfl,
  exact lt_of_lt_of_le (of_done h) (mono.of_done hp)
end

instance mmap' {l : list α} {f : α → parser β} [(f a).prog] [∀ a, (f a).mono] :
  ((a :: l).mmap' f).prog :=
begin
  constructor,
  simp only [and_imp, bind_eq_done, mmap', exists_imp_distrib, and_then_eq_bind],
  intros _ _ _ _ _ _ h hm,
  exact lt_of_lt_of_le (of_done h) (mono.of_done hm)
end

instance failure : @parser.prog α failure :=
⟨λ _ _ _ _, by simp⟩

lemma guard_true : ¬ prog (guard true) := pure _

instance guard : prog (guard false) :=
prog.failure

instance orelse [p.prog] [q.prog] : (p <|> q).prog :=
⟨λ _ _ _ _, by { simp_rw orelse_eq_done, rintro (h | ⟨h, -⟩); exact of_done h }⟩

instance decorate_errors [p.prog] :
  (@decorate_errors α msgs p).prog :=
⟨λ _ _ _ _, by { rw decorate_errors_eq_done, exact of_done }⟩

instance decorate_error [p.prog] : (@decorate_error α msg p).prog :=
prog.decorate_errors

instance any_char : prog any_char :=
begin
  constructor,
  intros cb n,
  by_cases h : n < cb.size,
  { simp_rw any_char_eq_done h,
    rintro _ - ⟨rfl, -⟩,
    exact lt_add_one n },
  { simp [any_char, h] }
end

instance sat {p : char → Prop} [decidable_pred p] : prog (sat p) :=
begin
  constructor,
  intros cb n,
  by_cases h : n < cb.size,
  { simp_rw sat_eq_done h,
    rintro _ - ⟨-, rfl, -⟩,
    exact lt_add_one n },
  { simp [sat, h] }
end

lemma eps : ¬ prog eps := prog.pure ()

instance ch {c : char} : prog (ch c) := prog.decorate_error

-- TODO: add prog.char_buf, needs char_buf_eq_done

instance one_of {cs : list char} : (one_of cs).prog :=
prog.decorate_errors

instance one_of' {cs : list char} : (one_of' cs).prog :=
prog.and_then

lemma str {s : string} (h : s ≠ "") : (str s).prog :=
begin
  obtain ⟨c, s', hs⟩ : ∃ c s', s.to_list = c :: s',
    { apply list.exists_cons_of_ne_nil,
      simpa [←string.to_list_empty, string.to_list_inj] using h },
  convert prog.decorate_error,
  rw hs,
  simpa using prog.mmap'
end

lemma remaining : ¬ remaining.prog :=
begin
  introI h,
  have : remaining (string.to_char_buffer "") 0 = done 0 0 := by simpa [remaining_eq_done],
  replace this : 0 < 0 := prog.of_done this,
  exact (lt_irrefl _) this
end

lemma eof : ¬ eof.prog :=
begin
  introI h,
  have : eof (string.to_char_buffer "") 0 = done 0 () := by simpa [remaining_eq_done],
  replace this : 0 < 0 := prog.of_done this,
  exact (lt_irrefl _) this
end

instance foldr_core {f : α → β → β} {b : β} [p.mono] [p.prog] :
  ∀ {reps : ℕ}, (foldr_core f p b reps).prog
| 0          := prog.failure
| (reps + 1) := begin
  simp_rw parser.foldr_core,
  -- convert prog.orelse,
  -- { apply_instance },
  -- { exact prog.pure }
end

instance foldr {f : α → β → β} [p.prog] : prog (foldr f p b) :=
⟨λ _ _, prog.foldr_core.le _ _⟩

instance foldl_core {f : α → β → α} {p : parser β} [p.prog] :
  ∀ {a : α} {reps : ℕ}, (foldl_core f a p reps).prog
| _ 0          := prog.failure
| _ (reps + 1) := begin
  convert prog.orelse,
  { convert prog.bind,
    { apply_instance },
    { exact λ _, foldl_core } },
  { exact prog.pure }
end

instance foldl {f : α → β → α} {p : parser β} [p.prog] : prog (foldl f a p) :=
⟨λ _ _, prog.foldl_core.le _ _⟩

instance many [p.prog] : p.many.prog :=
prog.foldr

instance many_char {p : parser char} [p.prog] : p.many_char.prog :=
prog.map

instance many' [p.prog] : p.many'.prog :=
prog.and_then

instance many1 [p.prog] : p.many1.prog :=
prog.seq

instance many_char1 {p : parser char} [p.prog] : p.many_char1.prog :=
prog.map

instance sep_by1 [p.prog] [sep.prog] : prog (sep_by1 sep p) :=
prog.seq

instance sep_by [p.prog] [sep.prog] : prog (sep_by sep p) :=
prog.orelse

lemma fix_core {F : parser α → parser α} (hF : ∀ (p : parser α), p.prog → (F p).prog) :
  ∀ (max_depth : ℕ), prog (fix_core F max_depth)
| 0               := prog.failure
| (max_depth + 1) := hF _ (fix_core _)

instance digit : digit.prog :=
prog.decorate_error

instance nat : nat.prog :=
prog.decorate_error

lemma fix {F : parser α → parser α} (hF : ∀ (p : parser α), p.prog → (F p).prog) :
  prog (fix F) :=
⟨λ _ _, by { convert prog.fix_core.le _ _, exact hF }⟩

end prog

end parser
