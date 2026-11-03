import RuleCore.Soroban.Host
import RuleCore.Theorems.Chain

/-!
# Theorems about the Soroban models

* **Storage is a map.** Reading a slot gives what was last written there; a
  write or a removal changes no other slot, so the three durabilities and
  every contract keep their own values; an operation on a key holding a
  muxed address is refused and changes nothing.
* **What `rule-eval` reads of a context.** A creation is a creation, which no
  rule allows; a `u32` is `other` of `u32Xdr`, as Perch's lowering reads it;
  `i128`, `u64`, `bool`, bytes, strings and symbols are read as themselves and
  nothing else is read as them; an address is read as its `ScAddress` XDR,
  which no two addresses share.
* **The contexts the host passes can be read.** Reading the host's encoding
  of contexts gives them back, so the facade refuses only contexts SDK 27
  does not know.
* **What `__check_auth` receives.** In every transaction, each `__check_auth`
  call receives contexts that are its payload's invocation tree in preorder,
  root first, so never an empty batch; a delegate receives the payload and
  contexts of the entry being authenticated.
* **The containment link.** In every transaction, each `require_auth` an
  authorization entry satisfies is for a context of that entry's tree, and
  that tree passed every `checkRules` step of the address's `__check_auth`:
  so a call the host lets through on an account's signature is allowed by
  every rule set the account's `__check_auth` checks with `rule-eval`
  (`Tx.run_authorized_allowed`).
-/

namespace RuleCore.Soroban

open RuleCore

/-! ## Storage -/

theorem Store.get_set (s : Store) (k : Slot) (v : Val) : (s.set k v).get k = some v := by
  simp [Store.get, Store.set]

/-- Finding with a predicate that implies the filter's finds the same entry
in the filtered list. -/
theorem find?_filter_of_imp {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ a, q a = true → p a = true) : (xs.filter p).find? q = xs.find? q := by
  rw [List.find?_filter]
  congr 1
  funext a
  by_cases hq : q a = true
  · simp [hq, h a hq]
  · simp [hq]

theorem Store.get_set_ne (s : Store) {k k' : Slot} (v : Val) (h : k' ≠ k) :
    (s.set k v).get k' = s.get k' := by
  simp only [Store.get, Store.set, List.find?_cons]
  have : decide (k = k') = false := by simp [Ne.symm h]
  rw [this]
  simp only
  rw [find?_filter_of_imp]
  intro e he
  simp only [decide_eq_true_eq] at he ⊢
  rw [he]; exact h

theorem Store.get_remove (s : Store) (k : Slot) : (s.remove k).get k = none := by
  simp only [Store.get, Store.remove, Option.map_eq_none_iff, List.find?_eq_none]
  intro e he
  simp only [List.mem_filter, decide_eq_true_eq] at he
  simpa using he.2

theorem Store.get_remove_ne (s : Store) {k k' : Slot} (h : k' ≠ k) :
    (s.remove k).get k' = s.get k' := by
  simp only [Store.get, Store.remove]
  rw [find?_filter_of_imp]
  intro e he
  simp only [decide_eq_true_eq] at he ⊢
  rw [he]; exact h

theorem Store.has_iff (s : Store) (k : Slot) : s.has k = true ↔ ∃ v, s.get k = some v := by
  simp [Store.has, Option.isSome_iff_exists]

/-- The same key under two durabilities is two slots. -/
theorem Store.get_set_durability (s : Store) (c : Address) {d d' : Durability} (key v : Val)
    (h : d' ≠ d) : (s.set ⟨c, d, key⟩ v).get ⟨c, d', key⟩ = s.get ⟨c, d', key⟩ :=
  Store.get_set_ne s v (by simp [h])

/-- Every contract keeps its own storage. -/
theorem Store.get_set_contract (s : Store) {c c' : Address} (d d' : Durability) (key key' v : Val)
    (h : c' ≠ c) : (s.set ⟨c, d, key⟩ v).get ⟨c', d', key'⟩ = s.get ⟨c', d', key'⟩ :=
  Store.get_set_ne s v (by simp [h])

theorem Op.apply_eq_none_iff (c : Address) (s : Store) (op : Op) :
    op.apply c s = none ↔ op.key.storable = false := by
  unfold Op.apply
  split
  · rename_i h
    simp only [h, Bool.true_eq_false, iff_false]
    cases op <;> simp
  · rename_i h
    simpa using h

theorem Val.storable_address (a : Address) : (Val.address a).storable = !a.muxed := by
  simp [Val.storable]

theorem Val.storable_muxed (id : UInt64) (key : Bytes) :
    (Val.address (.muxedAccount id key)).storable = false := by
  simp [Val.storable, Address.muxed]

/-! ## What `rule-eval` reads of a context -/

@[simp] theorem AuthFn.toChain_create (h s : Bytes) (args : List Val) :
    (AuthFn.create h s args).toChain = .create h := rfl

theorem AuthFn.toChain_contract (c : Address) (f : Bytes) (args : List Val) :
    (AuthFn.contract c f args).toChain = .call c.xdr f (args.map Val.toChain) := rfl

/-- No rule allows a creation context. -/
theorem AuthFn.allows_create (rs : Chain.RuleSet) (h s : Bytes) (args : List Val)
    (auth : List Chain.Signer) : rs.allows (AuthFn.create h s args).toChain auth = false := by
  simp

/-- A `u32` is read as `other` of its XDR, the reading Perch's lowering
compares a `u32` argument with. -/
theorem Val.toChain_u32 (v : UInt32) : (Val.u32 v).toChain = .other (Document.u32Xdr v) := rfl

theorem Val.toChain_eq_i128_iff (v : Val) (x : BitVec 128) :
    v.toChain = .i128 x ↔ v = .i128 x := by
  cases v <;> simp [Val.toChain]

theorem Val.toChain_eq_u64_iff (v : Val) (x : UInt64) : v.toChain = .u64 x ↔ v = .u64 x := by
  cases v <;> simp [Val.toChain]

theorem Val.toChain_eq_bool_iff (v : Val) (x : Bool) : v.toChain = .bool x ↔ v = .bool x := by
  cases v <;> simp [Val.toChain]

theorem Val.toChain_eq_bytes_iff (v : Val) (x : Bytes) : v.toChain = .bytes x ↔ v = .bytes x := by
  cases v <;> simp [Val.toChain]

theorem Val.toChain_eq_string_iff (v : Val) (x : Bytes) :
    v.toChain = .string x ↔ v = .string x := by
  cases v <;> simp [Val.toChain]

theorem Val.toChain_eq_symbol_iff (v : Val) (x : Bytes) :
    v.toChain = .symbol x ↔ v = .symbol x := by
  cases v <;> simp [Val.toChain]

theorem Val.toChain_eq_address_iff (v : Val) (x : Bytes) :
    v.toChain = .address x ↔ ∃ a, v = .address a ∧ a.xdr = x := by
  cases v <;> simp [Val.toChain]

/-! ### Addresses are read without collision -/

/-- The value of four big-endian bytes. -/
def ofBe32 : Bytes → Nat
  | [a, b, c, d] => a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat
  | _ => 0

theorem be32_length (n : Nat) : (be32 n).length = 4 := rfl

theorem ofBe32_be32 (n : Nat) : ofBe32 (be32 n) = n % 4294967296 := by
  simp only [be32, ofBe32, UInt8.toNat_ofNat']
  omega

theorem be32_inj {m n : Nat} (hm : m < 4294967296) (hn : n < 4294967296) (h : be32 m = be32 n) :
    m = n := by
  have := congrArg ofBe32 h
  rw [ofBe32_be32, ofBe32_be32] at this
  omega

theorem be64_length (n : Nat) : (be64 n).length = 8 := rfl

theorem be64_inj {m n : Nat} (hm : m < 18446744073709551616) (hn : n < 18446744073709551616)
    (h : be64 m = be64 n) : m = n := by
  simp only [be64] at h
  have ⟨h1, h2⟩ := List.append_inj h (by simp [be32_length])
  have e1 := be32_inj (by omega) (by omega) h1
  have e2 := be32_inj (by omega) (by omega) h2
  omega

theorem Address.xdr_injective {a b : Address} (h : a.xdr = b.xdr) : a = b := by
  cases a <;> cases b <;> simp only [Address.xdr, List.append_assoc] at h
  all_goals first
    | (have := congrArg (List.take 4) h; simp [be32] at this; done)
    | skip
  · simpa using List.append_cancel_left (List.append_cancel_left h)
  · simpa using List.append_cancel_left h
  · rename_i id key id' key'
    have h' := List.append_cancel_left h
    have ⟨h1, h2⟩ := List.append_inj h' (by simp [be64_length])
    have := be64_inj id.toNat_lt id'.toNat_lt h1
    simp only [Address.muxedAccount.injEq]
    exact ⟨UInt64.toNat_inj.mp this, h2⟩

/-- A rule condition naming an address holds exactly for that address. -/
theorem Val.toChain_eq_address_xdr_iff (v : Val) (a : Address) :
    v.toChain = .address a.xdr ↔ v = .address a := by
  rw [Val.toChain_eq_address_iff]
  constructor
  · rintro ⟨b, rfl, h⟩
    rw [Address.xdr_injective h]
  · rintro rfl
    exact ⟨a, rfl, rfl⟩

/-! ## Reading the host's encoding of contexts -/

/-- A context whose creation hash and salt are 32 bytes, as the host's are. -/
def AuthFn.WellFormed : AuthFn → Prop
  | .contract .. => True
  | .create h s _ => h.length = 32 ∧ s.length = 32

theorem isSym_sym (s : String) : isSym (sym s) s = true := by
  simp [isSym]

theorem AuthFn.ofVal_toVal (f : AuthFn) (hf : f.WellFormed) : AuthFn.ofVal f.toVal = some f := by
  cases f with
  | contract c fn args => simp [AuthFn.toVal, AuthFn.ofVal, isSym_sym]
  | create h s args =>
    obtain ⟨hh, hs⟩ := hf
    cases args with
    | nil => simp [AuthFn.toVal, AuthFn.ofVal, isSym_sym, wasmHash, bytes32, hh, hs]
    | cons a as =>
      simp [AuthFn.toVal, AuthFn.ofVal, wasmHash, bytes32, hh, hs, isSym, sym, Bytes.ofString]

theorem contextsOfVal_toVal (fs : List AuthFn) (hf : ∀ f ∈ fs, f.WellFormed) :
    contextsOfVal (.vec (fs.map AuthFn.toVal)) = some fs := by
  simp only [contextsOfVal]
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.map_cons, List.mapM_cons, AuthFn.ofVal_toVal f (hf f (by simp))]
    simp [ih fun g hg => hf g (by simp [hg])]

/-! ## Signed trees -/

theorem Invocation.preorder_node (f : AuthFn) (subs : List Invocation) :
    (Invocation.node f subs).preorder = f :: Invocation.preorderList subs := rfl

/-- A tree's contexts start with its root's, so they are never empty. -/
theorem Invocation.preorder_ne_nil (i : Invocation) : i.preorder ≠ [] := by
  cases i; simp [Invocation.preorder]

theorem Invocation.preorder_head (i : Invocation) : i.preorder.head? = some i.fn := by
  cases i; simp [Invocation.preorder, Invocation.fn]

theorem Invocation.mem_preorderList {i : Invocation} {is : List Invocation} (h : i ∈ is) :
    ∀ g ∈ i.preorder, g ∈ Invocation.preorderList is := by
  induction is with
  | nil => simp at h
  | cons j js ih =>
    intro g hg
    simp only [Invocation.preorderList, List.mem_append]
    rcases List.mem_cons.mp h with rfl | h
    · exact .inl hg
    · exact .inr (ih h g hg)

/-- Every node a path reaches is in the tree's preorder. -/
theorem Invocation.at_fn_mem : ∀ (i : Invocation) (p : List Nat) {n : Invocation},
    i.at p = some n → n.fn ∈ i.preorder
  | i, [], n, h => by
    simp only [Invocation.at, Option.some.injEq] at h
    subst h; cases i; simp [Invocation.preorder, Invocation.fn]
  | .node f subs, j :: p, n, h => by
    simp only [Invocation.at] at h
    split at h
    · rename_i c hc
      have hm : c ∈ subs := List.mem_of_getElem? hc
      have := Invocation.at_fn_mem c p h
      simp only [Invocation.preorder, List.mem_cons]
      exact .inr (Invocation.mem_preorderList hm _ this)
    · simp at h

/-- Following a path to a node, then to one of its children, reaches that
child. -/
theorem Invocation.at_append_child : ∀ (i : Invocation) (p : List Nat) {n c : Invocation} {k : Nat},
    i.at p = some n → n.subs[k]? = some c → i.at (p ++ [k]) = some c
  | i, [], n, c, k, h, hc => by
    simp only [Invocation.at, Option.some.injEq] at h
    subst h
    cases i with
    | node f subs => simp [Invocation.at, Invocation.subs] at hc ⊢; simp [hc]
  | .node f subs, j :: p, n, c, k, h, hc => by
    simp only [Invocation.at] at h
    simp only [List.cons_append, Invocation.at]
    split at h
    · rename_i d _
      exact Invocation.at_append_child d p h hc
    · simp at h

/-- The child the matching walk picks has the context being matched. -/
theorem firstFree_spec {ex : List (List Nat)} {p : List Nat} {f : AuthFn} :
    ∀ {cs : List Invocation} {i k : Nat}, firstFree ex p f cs i = some k →
      ∃ c, cs[k - i]? = some c ∧ c.fn = f ∧ i ≤ k
  | [], _, _, h => by simp [firstFree] at h
  | c :: cs, i, k, h => by
    unfold firstFree at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact ⟨c, by simp, hc.2, Nat.le_refl _⟩
    · obtain ⟨c', hc', hf, hle⟩ := firstFree_spec h
      refine ⟨c', ?_, hf, by omega⟩
      have : k - i = (k - (i + 1)) + 1 := by omega
      rw [this]
      simpa using hc'

/-- A match is a node of the entry's tree with the frame's context, and it
leaves the entry and the authentication as they were. -/
theorem Tracker.extend_spec {t t' : Tracker} {f : AuthFn} {allowRoot : Bool}
    (h : t.extend f allowRoot = some t') :
    t'.entry = t.entry ∧ t'.verified = t.verified ∧ f ∈ t.entry.root.preorder := by
  unfold Tracker.extend at h
  split at h
  · simp at h
  · split at h
    · rename_i p _
      split at h
      · rename_i n hn
        split at h
        · rename_i k hk
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨c, hc, hf, _⟩ := firstFree_spec hk
          refine ⟨rfl, rfl, ?_⟩
          rw [← hf]
          exact Invocation.at_fn_mem _ _ (Invocation.at_append_child _ _ hn (by simpa using hc))
        · simp at h
      · simp at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        refine ⟨rfl, rfl, ?_⟩
        rw [← hc.2]
        cases ht : t.entry.root
        simp [Invocation.preorder, Invocation.fn]
      · simp at h

/-! ## What a run records -/

/-- An event `__check_auth` may record for an entry with payload `pre` and
contexts `ctxs`: a read, a presence check, or a `__check_auth` call (the
account's own or a delegate's) with that payload and those contexts. -/
def AccountEvent (pre : Preimage) (ctxs : List AuthFn) : Event → Prop
  | .read .. | .found .. => True
  | .checkAuth _ pre' _ ctxs' => pre' = pre ∧ ctxs' = ctxs
  | .authorized .. => False

/-- The log grows from `l` to `l'` by events that all satisfy `P`. -/
def Grows (P : Event → Prop) (l l' : List Event) : Prop :=
  ∃ new, l' = l ++ new ∧ ∀ e ∈ new, P e

theorem Grows.refl (P : Event → Prop) (l : List Event) : Grows P l l :=
  ⟨[], by simp, by simp⟩

theorem Grows.trans {P : Event → Prop} {l₁ l₂ l₃ : List Event} (h₁ : Grows P l₁ l₂)
    (h₂ : Grows P l₂ l₃) : Grows P l₁ l₃ := by
  obtain ⟨n₁, rfl, h₁⟩ := h₁
  obtain ⟨n₂, rfl, h₂⟩ := h₂
  exact ⟨n₁ ++ n₂, by simp, fun e he => (List.mem_append.mp he).elim (h₁ e) (h₂ e)⟩

theorem Grows.mono {P Q : Event → Prop} {l l' : List Event} (h : Grows P l l')
    (hpq : ∀ e, P e → Q e) : Grows Q l l' := by
  obtain ⟨n, rfl, h⟩ := h
  exact ⟨n, rfl, fun e he => hpq e (h e he)⟩

theorem Grows.logged {P : Event → Prop} (w : World) {e : Event} (h : P e) :
    Grows P w.log (w.logged e).log :=
  ⟨[e], rfl, by simp [h]⟩

/-- A storage operation records at most a read or a presence check, and
leaves the trackers as they were. -/
theorem World.op_spec (w : World) (c : Address) (op : Op) :
    (w.op c op).2.trackers = w.trackers ∧
      Grows (fun e => (∃ c d k v, e = .read c d k v) ∨ (∃ c d k b, e = .found c d k b))
        w.log (w.op c op).2.log := by
  unfold World.op
  split
  · exact ⟨rfl, Grows.refl _ _⟩
  · rename_i obs s _
    split
    · exact ⟨rfl, Grows.logged _ (.inl ⟨_, _, _, _, rfl⟩)⟩
    · exact ⟨rfl, Grows.logged _ (.inr ⟨_, _, _, _, rfl⟩)⟩
    · exact ⟨rfl, Grows.refl _ _⟩

theorem World.op_account {w w' : World} {c : Address} {op : Op} {b : Bool}
    (h : w.op c op = (b, w')) (pre : Preimage) (ctxs : List AuthFn) :
    w'.trackers = w.trackers ∧ Grows (AccountEvent pre ctxs) w.log w'.log := by
  obtain ⟨ht, hg⟩ := World.op_spec w c op
  rw [h] at ht hg
  refine ⟨ht, hg.mono ?_⟩
  rintro e (⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩) <;> trivial

/-- `__check_auth`'s program leaves the trackers as they were, records only
reads, presence checks and `__check_auth` calls with the payload and
contexts it was given, and, when it accepts, every rule set it checks allows
every context. -/
theorem runAccount_spec (cfg : Config) (stack : List Address) (pre : Preimage)
    (ctxs : List AuthFn) (node : List Delegate) (path : List Nat) (acct : Address)
    (steps : List AccountStep) (used : List (List Nat)) (w : World) :
    (runAccount cfg stack pre ctxs node path acct steps used w).2.1.trackers = w.trackers ∧
    Grows (AccountEvent pre ctxs) w.log (runAccount cfg stack pre ctxs node path acct steps used w).2.1.log ∧
    ((runAccount cfg stack pre ctxs node path acct steps used w).1 = true →
      ∀ rs auth, AccountStep.checkRules rs auth ∈ steps →
        Chain.RuleSet.allowsAll rs (ctxs.map AuthFn.toChain) auth = true) := by
  fun_induction runAccount cfg stack pre ctxs node path acct steps used w
  case case1 => exact ⟨rfl, Grows.refl _ _, fun _ _ _ h => by simp at h⟩
  case case2 | case4 | case6 =>
    rename_i w0 w1 hop ih
    obtain ⟨ht, hg⟩ := World.op_account hop pre ctxs
    exact ⟨ih.1.trans ht, hg.trans ih.2.1,
      fun hok rs auth hm => ih.2.2 hok rs auth (by simpa using hm)⟩
  case case3 | case5 | case7 =>
    rename_i w0 w1 hop
    obtain ⟨ht, hg⟩ := World.op_account hop pre ctxs
    exact ⟨ht, hg, fun h => by simp at h⟩
  case case8 =>
    rename_i rs auth _ _ _ h ih
    have h : Chain.RuleSet.allowsAll rs (ctxs.map AuthFn.toChain) auth = true := by simpa using h
    simp only [h, ↓reduceIte]
    refine ⟨ih.1, ih.2.1, fun hok rs' auth' hm => ?_⟩
    rcases List.mem_cons.mp hm with he | hm
    · simp only [AccountStep.checkRules.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact h
    · exact ih.2.2 hok rs' auth' hm
  case case9 =>
    rename_i rs auth _ _ _ h
    have h : ¬ Chain.RuleSet.allowsAll rs (ctxs.map AuthFn.toChain) auth = true := by simpa using h
    split
    · contradiction
    · exact ⟨rfl, Grows.refl _ _, fun h => by simp at h⟩
  case case14 =>
    rename_i hin ih2 ih1
    simp only [hin] at ih2 ⊢
    obtain ⟨ht2, hg2, _⟩ := ih2
    exact ⟨ih1.1.trans ht2, (Grows.logged _ ⟨rfl, rfl⟩).trans (hg2.trans ih1.2.1),
      fun hok rs auth hm => ih1.2.2 hok rs auth (by simpa using hm)⟩
  case case15 =>
    rename_i hin ih2
    simp only [hin] at ih2 ⊢
    obtain ⟨ht2, hg2, _⟩ := ih2
    exact ⟨ht2, (Grows.logged _ ⟨rfl, rfl⟩).trans hg2, fun h => by simp at h⟩
  all_goals exact ⟨rfl, Grows.refl _ _, fun h => by simp at h⟩

/-- The entry passed every `checkRules` step of its address's
`__check_auth`: every rule set checked there allows every context of its
tree. -/
def Checked (cfg : Config) (e : Entry) : Prop :=
  ∀ rs auth, AccountStep.checkRules rs auth ∈ cfg.program e.address →
    Chain.RuleSet.allowsAll rs (e.root.preorder.map AuthFn.toChain) auth = true

/-- Every authenticated tracker's entry is checked. -/
def TrackersOk (cfg : Config) (ts : List Tracker) : Prop :=
  ∀ t ∈ ts, t.verified = true → Checked cfg t.entry

/-- What a run records: each `__check_auth` call receives its payload's tree
in preorder, and each `require_auth` an entry satisfies is for a context
every rule set the address's `__check_auth` checks allows. -/
def Event.Good (cfg : Config) : Event → Prop
  | .checkAuth _ pre _ ctxs => ctxs = pre.invocation.preorder
  | .authorized a f .entry => ∀ rs auth, AccountStep.checkRules rs auth ∈ cfg.program a →
      Chain.RuleSet.allows rs f.toChain auth = true
  | _ => True

/-- What `__check_auth` reads is the store as the call that required
authorization left it, the call's own instance writes included. -/
theorem runAccount_get (cfg : Config) (stack : List Address) (pre : Preimage)
    (ctxs : List AuthFn) (node : List Delegate) (path : List Nat) (acct : Address)
    (d : Durability) (k : Val) (rest : List AccountStep) (used : List (List Nat)) (w : World)
    (hk : k.storable = true) :
    runAccount cfg stack pre ctxs node path acct (.get d k :: rest) used w =
      runAccount cfg stack pre ctxs node path acct rest used
        (w.logged (.read acct d k (w.store.get ⟨acct, d, k⟩))) := by
  rw [runAccount]
  simp [World.op, Op.apply, Op.key, Op.durability, hk]

/-- `__check_auth` runs on the world the requiring call left: authenticating
an entry runs its address's program on that world's store. -/
theorem authenticate_store (cfg : Config) (stack : List Address) (e : Entry) (w : World)
    (id : Bytes) (ha : e.address = .contract id)
    (hs : ¬ (e.address ∈ stack ∧ stack.getLast? ≠ some e.address)) :
    authenticate cfg stack e w =
      let r := runAccount cfg (stack ++ [e.address]) e.preimage e.root.preorder e.delegates [] e.address
        (cfg.program e.address) [] (w.logged (.checkAuth e.address e.preimage e.signature e.root.preorder))
      (r.1, r.2.1) := by
  unfold authenticate
  split
  · exact absurd ‹_› hs
  · split
    · rfl
    · rename_i h; exact absurd ha (h id)

/-- `__check_auth` of an entry leaves the trackers as they were, records only
reads, presence checks and `__check_auth` calls (its address's and its
delegates') that receive the entry's payload and its tree's contexts, and,
when it accepts, the entry is checked. -/
theorem authenticate_spec (cfg : Config) (stack : List Address) (e : Entry) (w : World) :
    (authenticate cfg stack e w).2.trackers = w.trackers ∧
    Grows (AccountEvent e.preimage e.root.preorder) w.log (authenticate cfg stack e w).2.log ∧
    ((authenticate cfg stack e w).1 = true → Checked cfg e) := by
  unfold authenticate
  split
  · exact ⟨rfl, Grows.refl _ _, fun h => by simp at h⟩
  · split
    · obtain ⟨ht, hg, hc⟩ := runAccount_spec cfg (stack ++ [e.address]) e.preimage e.root.preorder
        e.delegates [] e.address (cfg.program e.address) []
        (w.logged (.checkAuth e.address e.preimage e.signature e.root.preorder))
      exact ⟨ht, (Grows.logged _ ⟨rfl, rfl⟩).trans hg, fun h rs auth hm => hc h rs auth hm⟩
    · exact ⟨rfl, Grows.refl _ _, fun h => by simp at h⟩

theorem AccountEvent.good {cfg : Config} {e : Entry} {ev : Event}
    (h : AccountEvent e.preimage e.root.preorder ev) : ev.Good cfg := by
  cases ev with
  | checkAuth a pre sig ctxs =>
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | read => trivial
  | found => trivial
  | authorized => exact h.elim

theorem findTracker_spec {f : AuthFn} {a : Address} {allowRoot : Bool} :
    ∀ {ts : List Tracker} {i j : Nat} {t' : Tracker}, findTracker f a allowRoot ts i = some (j, t') →
      i ≤ j ∧ ∃ t, ts[j - i]? = some t ∧ t.entry.address = a ∧ t.extend f allowRoot = some t'
  | [], _, _, _, h => by simp [findTracker] at h
  | t :: ts, i, j, t', h => by
    unfold findTracker at h
    split at h
    · rename_i ha
      split at h
      · rename_i t'' ht
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨Nat.le_refl _, t, by simp, ha, ht⟩
      · obtain ⟨hle, u, hu, hua, hue⟩ := findTracker_spec h
        refine ⟨by omega, u, ?_, hua, hue⟩
        have : j - i = (j - (i + 1)) + 1 := by omega
        rw [this]; simpa using hu
    · obtain ⟨hle, u, hu, hua, hue⟩ := findTracker_spec h
      refine ⟨by omega, u, ?_, hua, hue⟩
      have : j - i = (j - (i + 1)) + 1 := by omega
      rw [this]; simpa using hu

theorem TrackersOk.set {cfg : Config} {ts : List Tracker} (h : TrackersOk cfg ts) (i : Nat)
    {t : Tracker} (ht : t.verified = true → Checked cfg t.entry) : TrackersOk cfg (ts.set i t) := by
  intro u hu hv
  rcases List.mem_or_eq_of_mem_set hu with hu | rfl
  · exact h u hu hv
  · exact ht hv

/-- An entry's checked tree allows each of its contexts. -/
theorem Checked.allows {cfg : Config} {e : Entry} (h : Checked cfg e) {f : AuthFn}
    (hf : f ∈ e.root.preorder) : ∀ rs auth, AccountStep.checkRules rs auth ∈ cfg.program e.address →
      Chain.RuleSet.allows rs f.toChain auth = true := by
  intro rs auth hm
  have := h rs auth hm
  rw [Chain.RuleSet.allowsAll_iff] at this
  exact this _ (List.mem_map_of_mem hf)

theorem requireAuth_spec (cfg : Config) (stack : List Address) (f : AuthFn) (a : Address)
    (w : World) (hw : TrackersOk cfg w.trackers) :
    TrackersOk cfg (requireAuth cfg stack f a w).2.trackers ∧
      Grows (Event.Good cfg) w.log (requireAuth cfg stack f a w).2.log := by
  unfold requireAuth
  split
  · exact ⟨hw, Grows.logged _ trivial⟩
  · dsimp only
    split
    · exact ⟨hw, Grows.refl _ _⟩
    · rename_i i t hfind
      obtain ⟨_, t0, ht0, hta, hext⟩ := findTracker_spec hfind
      simp only [Nat.sub_zero] at ht0
      obtain ⟨hentry, hver, hf⟩ := Tracker.extend_spec hext
      have ht0m : t0 ∈ w.trackers := List.mem_of_getElem? ht0
      have hok : TrackersOk cfg (w.trackers.set i t) :=
        hw.set i fun hv => hentry ▸ hw t0 ht0m (hver ▸ hv)
      have haddr : t.entry.address = a := hentry ▸ hta
      have hmem : f ∈ t.entry.root.preorder := hentry ▸ hf
      split
      · rename_i hv
        refine ⟨hok, Grows.logged _ ?_⟩
        exact haddr ▸ Checked.allows (hentry ▸ hw t0 ht0m (hver ▸ hv)) hmem
      · obtain ⟨hat, hag, hac⟩ := authenticate_spec cfg stack t.entry
          { w with trackers := w.trackers.set i t }
        have hag : Grows (Event.Good cfg) w.log _ := hag.mono fun _ h => AccountEvent.good h
        split
        · rename_i w' hres
          rw [hres] at hat hag
          exact ⟨hat ▸ hok, hag⟩
        · rename_i w' hres
          rw [hres] at hat hag hac
          have hchk := hac rfl
          split
          · exact ⟨hat ▸ hok, hag⟩
          · split
            · exact ⟨hat ▸ hok, hag⟩
            · refine ⟨hat ▸ hok.set i fun _ => hchk, hag.trans (Grows.logged _ ?_)⟩
              exact haddr ▸ Checked.allows hchk hmem

theorem TrackersOk.push {cfg : Config} {ts : List Tracker} (h : TrackersOk cfg ts) :
    TrackersOk cfg (ts.map Tracker.push) := by
  intro t ht hv
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact h u hu hv

theorem TrackersOk.pop {cfg : Config} {ts : List Tracker} (h : TrackersOk cfg ts) :
    TrackersOk cfg (ts.map Tracker.pop) := by
  intro t ht hv
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact h u hu hv

mutual

theorem execCall_spec (cfg : Config) : ∀ (stack : List Address) (c : Call) (w : World),
    TrackersOk cfg w.trackers →
      TrackersOk cfg (execCall cfg stack c w).2.trackers ∧
        Grows (Event.Good cfg) w.log (execCall cfg stack c w).2.log
  | stack, .mk c fn args body, w, hw => by
    unfold execCall
    split
    · exact ⟨hw, Grows.refl _ _⟩
    · obtain ⟨h2, g2⟩ := execSteps_spec cfg (stack ++ [c]) (.contract c fn args) c body
        { w with trackers := w.trackers.map Tracker.push } hw.push
      dsimp only
      split
      · exact ⟨h2.pop, g2⟩
      · exact ⟨hw.push.pop, g2⟩

theorem execSteps_spec (cfg : Config) (stack : List Address) (f : AuthFn) (self : Address) :
    ∀ (steps : List Step) (w : World), TrackersOk cfg w.trackers →
      TrackersOk cfg (execSteps cfg stack f self steps w).2.trackers ∧
        Grows (Event.Good cfg) w.log (execSteps cfg stack f self steps w).2.log
  | [], w, hw => ⟨hw, Grows.refl _ _⟩
  | s :: rest, w, hw => by
    unfold execSteps
    obtain ⟨h1, g1⟩ := execStep_spec cfg stack f self s w hw
    dsimp only
    split
    · obtain ⟨h2, g2⟩ := execSteps_spec cfg stack f self rest _ h1
      exact ⟨h2, g1.trans g2⟩
    · exact ⟨h1, g1⟩

theorem execStep_spec (cfg : Config) (stack : List Address) (f : AuthFn) (self : Address) :
    ∀ (s : Step) (w : World), TrackersOk cfg w.trackers →
      TrackersOk cfg (execStep cfg stack f self s w).2.trackers ∧
        Grows (Event.Good cfg) w.log (execStep cfg stack f self s w).2.log
  | .get d k, w, hw | .has d k, w, hw | .put d k _, w, hw | .remove d k, w, hw => by
    unfold execStep
    obtain ⟨ht, hg⟩ := World.op_spec w self _
    refine ⟨ht ▸ hw, hg.mono ?_⟩
    rintro e (⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩) <;> trivial
  | .requireAuth a, w, hw => by
    unfold execStep
    exact requireAuth_spec cfg stack f a w hw
  | .call c catches, w, hw => by
    unfold execStep
    obtain ⟨h1, g1⟩ := execCall_spec cfg stack c w hw
    dsimp only
    split
    · exact ⟨h1, g1⟩
    · exact ⟨h1, g1⟩
  | .fail _, w, hw => ⟨hw, Grows.refl _ _⟩

end

/-- Every event a transaction records is good. -/
theorem Tx.run_good (accounts : List (Address × List AccountStep)) (tx : Tx) (w : World) :
    Grows (Event.Good ⟨accounts, tx.ledger⟩) w.log (tx.run accounts w).2.log := by
  have hw : TrackersOk ⟨accounts, tx.ledger⟩ (tx.entries.map Tracker.ofEntry) := by
    intro t ht hv
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp ht
    simp [Tracker.ofEntry] at hv
  exact (execCall_spec _ [] tx.call { w with trackers := tx.entries.map Tracker.ofEntry } hw).2

/-- **The containment link.** In every transaction, each `require_auth` that
an authorization entry satisfies, for address `a` in a frame whose context is
`f`, has `f` allowed by every rule set that `a`'s `__check_auth` checks with
`rule-eval`. -/
theorem Tx.run_authorized_allowed (accounts : List (Address × List AccountStep)) (tx : Tx)
    (w : World) :
    ∃ new, (tx.run accounts w).2.log = w.log ++ new ∧
      ∀ a f, Event.authorized a f .entry ∈ new → ∀ rs auth,
        AccountStep.checkRules rs auth ∈ Config.program ⟨accounts, tx.ledger⟩ a →
          Chain.RuleSet.allows rs f.toChain auth = true := by
  obtain ⟨new, h, hg⟩ := Tx.run_good accounts tx w
  exact ⟨new, h, fun a f he => hg _ he⟩

/-- In every transaction, each `__check_auth` call receives as its contexts
its payload's invocation tree in preorder, root first, so never an empty
batch. -/
theorem Tx.run_checkAuth_contexts (accounts : List (Address × List AccountStep)) (tx : Tx)
    (w : World) :
    ∃ new, (tx.run accounts w).2.log = w.log ++ new ∧
      ∀ a pre sig ctxs, Event.checkAuth a pre sig ctxs ∈ new →
        ctxs = pre.invocation.preorder ∧ ctxs ≠ [] ∧ ctxs.head? = some pre.invocation.fn := by
  obtain ⟨new, h, hg⟩ := Tx.run_good accounts tx w
  refine ⟨new, h, fun a pre sig ctxs he => ?_⟩
  have hc : ctxs = pre.invocation.preorder := hg _ he
  subst hc
  exact ⟨rfl, Invocation.preorder_ne_nil _, Invocation.preorder_head _⟩

/-- Authenticating an entry, every `__check_auth` call, its address's and
each delegate's, receives the entry's payload and its tree's contexts. -/
theorem authenticate_checkAuth (cfg : Config) (stack : List Address) (e : Entry) (w : World) :
    ∃ new, (authenticate cfg stack e w).2.log = w.log ++ new ∧
      ∀ a pre sig ctxs, Event.checkAuth a pre sig ctxs ∈ new →
        pre = e.preimage ∧ ctxs = e.root.preorder := by
  obtain ⟨_, ⟨new, h, hg⟩, _⟩ := authenticate_spec cfg stack e w
  exact ⟨new, h, fun a pre sig ctxs he => hg _ he⟩

/-- The payload binds the address exactly for `ADDRESS_V2` and delegated
credentials. -/
theorem Entry.preimage_address (e : Entry) :
    e.preimage.address = match e.credentials with
      | .address => none
      | _ => some e.address := rfl

/-! ## Rollback -/

/-- A failed call leaves the store and the used nonces as they were before
it. -/
theorem execCall_fail (cfg : Config) (stack : List Address) (c : Call) (w : World)
    (h : (execCall cfg stack c w).1 = false) :
    (execCall cfg stack c w).2.store = w.store ∧ (execCall cfg stack c w).2.nonces = w.nonces := by
  cases c with
  | mk c fn args body =>
    unfold execCall at h ⊢
    split
    · exact ⟨rfl, rfl⟩
    · rename_i hin
      simp only [hin, ↓reduceIte] at h
      dsimp only
      split
      · rename_i hok
        exact absurd hok (by simp [h])
      · exact ⟨rfl, rfl⟩

/-- A caught failure is a successful step that leaves the store and the used
nonces as they were before the call. -/
theorem execStep_call_caught (cfg : Config) (stack : List Address) (f : AuthFn) (self : Address)
    (c : Call) (w : World) (h : (execCall cfg stack c w).1 = false) :
    (execStep cfg stack f self (.call c true) w).1 = true ∧
      (execStep cfg stack f self (.call c true) w).2.store = w.store ∧
      (execStep cfg stack f self (.call c true) w).2.nonces = w.nonces := by
  unfold execStep
  simp only [h, Bool.false_eq_true, ↓reduceIte]
  exact ⟨trivial, execCall_fail cfg stack c w h⟩

/-- An uncaught failure fails the caller. -/
theorem execStep_call_uncaught (cfg : Config) (stack : List Address) (f : AuthFn) (self : Address)
    (c : Call) (w : World) (h : (execCall cfg stack c w).1 = false) :
    (execStep cfg stack f self (.call c false) w).1 = false := by
  unfold execStep
  simp [h]

/-- A failed transaction leaves storage and the used nonces as they were, so
a replay of its entries is not refused for it. -/
theorem Tx.run_fail (accounts : List (Address × List AccountStep)) (tx : Tx) (w : World)
    (h : (tx.run accounts w).1 = false) :
    (tx.run accounts w).2.store = w.store ∧ (tx.run accounts w).2.nonces = w.nonces :=
  execCall_fail _ [] tx.call { w with trackers := tx.entries.map Tracker.ofEntry } h

end RuleCore.Soroban
