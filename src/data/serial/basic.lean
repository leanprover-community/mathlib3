
import tactic
import tactic.monotonicity
import tactic.norm_num
import category.basic
-- import category.nursery
-- import data.equiv.nursery
import data.serial.medium

universes u v w

abbreviation put_m' := medium.put_m'.{u} unsigned
abbreviation put_m  := medium.put_m'.{u} unsigned punit
abbreviation get_m  := medium.get_m.{u} unsigned

def serial_inverse {α : Type u} (encode : α → put_m) (decode : get_m α) : Prop :=
∀ w, decode -<< encode w = pure w

class serial (α : Type u) :=
  (encode : α → put_m)
  (decode : get_m α)
  (correctness : ∀ w, decode -<< encode w = pure w)

class serial1 (f : Type u → Type v) :=
  (encode : Π {α}, (α → put_m) → f α → put_m)
  (decode : Π {α}, get_m α → get_m (f α))
  (correctness : ∀ {α} put get, serial_inverse.{u} put get →
                 ∀ (w : f α), decode get -<< encode put w = pure w)

instance serial.serial1 {f α} [serial1 f] [serial α] : serial (f α) :=
{ encode := λ x, serial1.encode serial.encode x,
  decode := serial1.decode f (serial.decode α),
  correctness := serial1.correctness _ _ serial.correctness }

class serial2 (f : Type u → Type v → Type w) :=
  (encode : Π {α β}, (α → put_m.{u}) → (β → put_m.{v}) → f α β → put_m.{w})
  (decode : Π {α β}, get_m α → get_m β → get_m (f α β))
  (correctness : ∀ {α β} putα getα putβ getβ,
                   serial_inverse putα getα →
                   serial_inverse putβ getβ →
                 ∀ (w : f α β), decode getα getβ -<< encode putα putβ w = pure w)

instance serial.serial2 {f α β} [serial2 f] [serial α] [serial β] : serial (f α β) :=
{ encode := λ x, serial2.encode serial.encode serial.encode x,
  decode := serial2.decode f (serial.decode _) (serial.decode _),
  correctness := serial2.correctness _ _ _ _ serial.correctness serial.correctness }

instance serial1.serial2 {f α} [serial2 f] [serial α] : serial1 (f α) :=
{ encode := λ β put x, serial2.encode serial.encode put x,
  decode := λ β get, serial2.decode f (serial.decode _) get,
  correctness := λ β get put, serial2.correctness _ _ _ _ serial.correctness  }

export serial (encode decode)

namespace serial

open function
export medium (hiding put_m get_m put_m')

variables {α β σ γ : Type u} {ω : Type}

def serialize [serial α] (x : α) : list unsigned := (encode x).eval
def deserialize (α : Type u) [serial α] (bytes : list unsigned) : option α := (decode α).eval bytes

lemma deserialize_serialize  [serial α] (x : α) :
  deserialize _ (serialize x) = some x :=
by simp [deserialize,serialize,eval_eval,serial.correctness]; refl

lemma encode_decode_bind [serial α]
  (f : α → get_m β) (f' : punit → put_m) (w : α) :
  (decode α >>= f) -<< (encode w >>= f') = f w -<< f' punit.star :=
by { rw [read_write_mono]; rw serial.correctness; refl }

lemma encode_decode_bind' [serial α]
  (f : α → get_m β) (w : α) :
  (decode α >>= f) -<< (encode w) = f w -<< pure punit.star :=
by { rw [read_write_mono_left]; rw serial.correctness; refl }

lemma encode_decode_pure
  (w w' : α) (u : punit) :
  (pure w : get_m α) -<< (pure u) = pure w' ↔ w = w' :=
by split; intro h; cases h; refl

open ulift

protected def ulift.encode [serial α] (w : ulift.{v} α) : put_m :=
(liftable1.up _ equiv.punit_equiv_punit (encode (down w) : medium.put_m' unsigned _) : medium.put_m' unsigned _)

protected def ulift.decode [serial α] : get_m (ulift α) :=
get_m.up ulift.up (decode α)

instance [serial α] : serial (ulift.{v u} α) :=
{ encode := ulift.encode
, decode := ulift.decode
, correctness :=
  by { introv, simp [ulift.encode,ulift.decode],
       rw up_read_write' _ equiv.ulift.symm,
       rw [serial.correctness], cases w, refl,
       intro, refl } }

instance unsigned.serial : serial unsigned :=
{ encode := λ w, put_m'.write w put_m'.pure
, decode := get_m.read get_m.pure
, correctness := by introv; refl }

-- protected def write_word (w : unsigned) : put_m :=
-- encode (up.{u} w)

@[simp] lemma loop_read_write_word {α β γ : Type u}
  (w : unsigned) (x : α) (f : α → unsigned → get_m (β ⊕ α)) (g : β → get_m γ)
  (rest : punit → put_m) :
  get_m.loop f g x -<< (write_word w >>= rest) =
  (f x w >>= get_m.loop.rest f g) -<< rest punit.star := rfl

@[simp] lemma loop_read_write_word' {α β γ : Type u}
  (w : unsigned) (x : α) (f : α → unsigned → get_m (β ⊕ α)) (g : β → get_m γ)  :
  get_m.loop f g x -<< (write_word w) =
  (f x w >>= get_m.loop.rest f g) -<< pure punit.star := rfl

-- protected def read_word : get_m.{u} (ulift unsigned) :=
-- decode _

def select_tag' (tag : unsigned) : list (unsigned × get_m α) → get_m α
| [] := get_m.fail
| ((w,x) :: xs) := if w = tag then x else select_tag' xs

def select_tag (xs : list (unsigned × get_m α)) : get_m α :=
do w ← read_word,
   select_tag' (down w) xs

@[simp]
lemma read_write_tag_hit {w w' : unsigned} {x : get_m α}
  {xs : list (unsigned × get_m α)} {y : put_m}
  (h : w = w') :
  select_tag ( (w,x) :: xs ) -<< (write_word w' >> y) = x -<< y :=
by subst w'; simp [select_tag,(>>),encode_decode_bind,select_tag']

lemma read_write_tag_hit' {w w' : unsigned} {x : get_m α}
  {xs : list (unsigned × get_m α)}
  (h : w = w') :
  select_tag ( (w,x) :: xs ) -<< (write_word w') = x -<< pure punit.star :=
by subst w'; simp [select_tag,(>>),encode_decode_bind',select_tag']

@[simp]
lemma read_write_tag_miss {w w' : unsigned} {x : get_m α}
  {xs : list (unsigned × get_m α)} {y : put_m}
  (h : w ≠ w') :
  select_tag ( (w,x) :: xs ) -<< (write_word w' >> y) = select_tag xs -<< (write_word w' >> y) :=
by simp [select_tag,(>>),encode_decode_bind,select_tag',*]

def recursive_parser {α} : ℕ → (get_m α → get_m α) → get_m α
| 0 _ := get_m.fail
| (nat.succ n) rec_fn := rec_fn $ recursive_parser n rec_fn

lemma recursive_parser_unfold {α} (n : ℕ) (f : get_m α → get_m α) (h : 1 ≤ n) :
  recursive_parser n f = f (recursive_parser (n-1) f) :=
by cases n; [ cases h, refl ]

attribute [simp] serial.correctness

end serial

structure serializer (α : Type u) (β : Type u) :=
(encoder : α → put_m.{u})
(decoder : get_m β)

def serial.mk_serializer' (α) [serial α] : serializer α α :=
{ encoder := encode,
  decoder := decode α }

namespace serializer

def valid_serializer {α} (x : serializer α α) :=
serial_inverse
      (serializer.encoder x)
      (serializer.decoder x)

lemma serializer.eq {α β} (x y : serializer α β)
  (h : x.encoder = y.encoder)
  (h' : x.decoder = y.decoder) :
  x = y :=
by cases x; cases y; congr; assumption

namespace serializer.seq

variables {α : Type u} {i j : Type u}
variables (x : serializer α (i → j))
variables (y : serializer α i)

def encoder := λ (k : α), (x.encoder k >> y.encoder k : put_m' _)
def decoder := x.decoder <*> y.decoder

end serializer.seq

instance {α : Type u} : applicative (serializer.{u} α) :=
{ pure := λ i x, { encoder := λ _, (return punit.star : put_m' _), decoder := pure x }
, seq := λ i j x y,
  { encoder := serializer.seq.encoder x y
  , decoder := serializer.seq.decoder x y } }

section lawful_applicative

variables {α β : Type u} {σ : Type u}

@[simp]
lemma decoder_pure (x : β) :
  (pure x : serializer σ β).decoder = pure x := rfl

@[simp]
lemma decoder_map (f : α → β) (x : serializer σ α) :
  (f <$> x).decoder = f <$> x.decoder := rfl

@[simp]
lemma decoder_seq (f : serializer σ (α → β)) (x : serializer σ α) :
  (f <*> x).decoder = f.decoder <*> x.decoder := rfl

@[simp]
lemma encoder_pure (x : β) (w : σ) :
  (pure x : serializer σ β).encoder w = (pure punit.star : put_m' _) := rfl

@[simp]
lemma encoder_map (f : α → β) (w : σ) (x : serializer σ α) :
  (f <$> x : serializer σ β).encoder w = x.encoder w := rfl

@[simp]
lemma encoder_seq (f : serializer σ (α → β)) (x : serializer σ α) (w : σ) :
  (f <*> x : serializer σ β).encoder w = (f.encoder w >> x.encoder w : put_m' _) := rfl

end lawful_applicative

instance {α} : is_lawful_functor (serializer.{u} α) :=
by refine { .. }; intros; apply serializer.eq; try { ext }; simp [map_map]

instance {α} : is_lawful_applicative (serializer.{u} α) :=
by{  constructor; intros; apply serializer.eq; try { ext };
     simp [(>>),pure_seq_eq_map,seq_assoc,bind_assoc],  }

protected def up {β} (ser : serializer β β) : serializer (ulift.{u v} β) (ulift.{u v} β) :=
{ encoder := pliftable.up' _ ∘ ser.encoder ∘ ulift.down,
  decoder := medium.get_m.up ulift.up ser.decoder }

def ser_field_with {α β} (ser : serializer β β) (f : α → β) : serializer α β :=
{ encoder := ser.encoder ∘ f,
  decoder := ser.decoder }

@[simp]
def ser_field_with' {α β} (ser : serializer β β) (f : α → β) : serializer.{max u v} α (ulift.{v} β) :=
ser_field_with ser.up (ulift.up ∘ f)

@[simp]
def ser_field {α β} [serial β] (f : α → β) : serializer α β :=
ser_field_with (serial.mk_serializer' β) f

@[simp]
lemma valid_mk_serializer (α) [serial α] :
  valid_serializer (serial.mk_serializer' α) :=
serial.correctness

variables {α β σ γ : Type u} {ω : Type}

def there_and_back_again
  (y : serializer γ α) (w : γ) : option α :=
y.decoder -<< y.encoder w

open medium (hiding put_m put_m' get_m)

lemma there_and_back_again_seq {ser : serializer α α}
  {x : serializer γ (α → β)} {f : α → β} {y : γ → α} {w : γ} {w' : β}
  (h' : there_and_back_again x w = pure f)
  (h : w' = f (y w))
  (h₀ : valid_serializer ser) :
  there_and_back_again (x <*> ser_field_with ser y) w = pure w' :=
by { simp [there_and_back_again,(>>),seq_eq_bind_map] at *,
     rw [read_write_mono h',map_read_write],
     rw [ser_field_with,h₀], subst w', refl }

lemma there_and_back_again_map {ser : serializer α α}
  {f : α → β} {y : γ → α} {w : γ}
  (h₀ : valid_serializer ser) :
  there_and_back_again (f <$> ser_field_with ser y) w = pure (f $ y w) :=
by rw [← pure_seq_eq_map,there_and_back_again_seq]; refl <|> assumption

lemma there_and_back_again_pure (x : β) (w : γ) :
  there_and_back_again (pure x) w =
  pure x := rfl

lemma valid_serializer_of_there_and_back_again
      {α : Type*} (y : serializer α α) :
  valid_serializer y ↔
  ∀ (w : α), there_and_back_again y w = pure w :=
by { simp [valid_serializer,serial_inverse],
     repeat { rw forall_congr, intro }, refl }

@[simp]
lemma valid_serializer_up (x: serializer α α) :
  valid_serializer (serializer.up.{v} x) ↔ valid_serializer x :=
by { cases x, simp [valid_serializer,serializer.up,serial_inverse,equiv.forall_iff_forall equiv.ulift],
     apply forall_congr, intro, dsimp [equiv.ulift,pliftable.up'],
     rw up_read_write' _ equiv.ulift.symm, split; intro h,
     { replace h := congr_arg (liftable1.down.{u} option (equiv.symm equiv.ulift)) h,
       simp [liftable1.down_up] at h, simp [h], refl },
     { simp [h], refl },
     { intro, refl, } }

open ulift

def ser_field' {α β} [serial β] (f : α → β) : serializer.{max u v} α (ulift.{v} β) :=
ser_field (up ∘ f)

def put₀ {α} (x : α) : put_m.{u} := (pure punit.star : put_m' _)
def get₀ {α} : get_m α := get_m.fail

def of_encoder {α} (x : α → put_m) : serializer α α :=
⟨ x, get₀ ⟩

def of_decoder {α} (x : get_m α) : serializer α α :=
⟨ put₀, x ⟩

section applicative

@[simp]
lemma encoder_ser_field (f : β → α) (x : serializer α α) (w : β) :
  (ser_field_with x f).encoder w = x.encoder (f w) := rfl

@[simp]
lemma encoder_up (x : serializer α α) (w : ulift α) :
  (serializer.up x).encoder w = pliftable.up' _ (x.encoder $ w.down) := rfl

@[simp]
lemma encoder_of_encoder (x : α → put_m) (w : α) :
  (of_encoder x).encoder w = x w := rfl

@[simp]
lemma decoder_ser_field (f : β → α) (x : serializer α α) :
  (ser_field_with x f).decoder = x.decoder := rfl

@[simp]
lemma decoder_up (x : serializer α α) :
  (serializer.up x).decoder = (x.decoder).up ulift.up := rfl

@[simp]
lemma decoder_of_decoder (x : get_m α) :
  (of_decoder x).decoder = x := rfl

end applicative
end serializer

namespace serial

open serializer

def of_serializer {α} (s : serializer α α)
  (h : ∀ w, there_and_back_again s w = pure w) : serial α :=
{ encode := s.encoder
, decode := s.decoder
, correctness := @h }

def of_serializer₁ {f : Type u → Type v}
  (s : Π α, serializer α α → serializer (f α) (f α))
  (h : ∀ α ser, valid_serializer ser →
       ∀ w, there_and_back_again (s α ser) w = pure w)
  (h₀ : ∀ {α} ser w, (s α (of_encoder (encoder ser))).encoder w = (s α ser).encoder w)
  (h₁ : ∀ {α} ser, (s α (of_decoder (decoder ser))).decoder = (s α ser).decoder) : serial1 f :=
{ encode := λ α put, (s α (of_encoder put)).encoder
, decode := λ α get, (s α (of_decoder get)).decoder
, correctness := by { introv hh, simp [h₀ ⟨put, get⟩,h₁ ⟨put,get⟩], apply h; assumption } }

def of_serializer₂ {f : Type u → Type v → Type w}
  (s : Π α β, serializer α α →
              serializer β β →
              serializer (f α β) (f α β))
  (h : ∀ α β serα serβ, valid_serializer serα → valid_serializer serβ →
       ∀ w, there_and_back_again (s α β serα serβ) w = pure w)
  (h₀ : ∀ {α β} serα serβ w, (s α β (of_encoder (encoder serα)) (of_encoder (encoder serβ))).encoder w = (s α β serα serβ).encoder w)
  (h₁ : ∀ {α β} serα serβ, (s α β (of_decoder (decoder serα)) (of_decoder (decoder serβ))).decoder = (s α β serα serβ).decoder) : serial2 f :=
{ encode := λ α β putα putβ, (s α β (of_encoder putα) (of_encoder putβ)).encoder
, decode := λ α β getα getβ, (s α β (of_decoder getα) (of_decoder getβ)).decoder
, correctness := by { introv hα hβ, simp [h₀ ⟨putα,getα⟩ ⟨putβ,getβ⟩,h₁ ⟨putα,getα⟩ ⟨putβ,getβ⟩],
                      apply h; assumption } }

end serial

namespace tactic
open interactive
open interactive.types
open lean.parser

meta def interactive.mk_serializer (p : parse texpr) : tactic unit :=
do g ← mk_mvar,
   refine ``(serial.of_serializer %%p %%g) <|>
     refine ``(serial.of_serializer₁ (λ α ser, %%p) %%g _ _) <|>
     refine ``(serial.of_serializer₂ (λ α β ser_α ser_β, %%p) %%g _ _),
   gs ← get_goals,
   set_goals [g],
   vs ← intros,
   cases vs.ilast,
   iterate $
     applyc ``serializer.there_and_back_again_map <|>
     applyc ``serializer.there_and_back_again_pure <|>
     applyc ``serializer.there_and_back_again_seq,
  gs' ← get_goals,
  set_goals (gs ++ gs'),
  repeat $
    intros >>
    `[simp *] <|>
    reflexivity

end tactic
