def injective {A B : Type} (f : A → B) : Prop := ∀{a1 a2 : A}, (f a1 = f a2) → (a1 = a2)
def monomorphism {A B : Type} (f : A → B) : Prop := ∀{C : Type}, ∀{g h : C → A}, f ∘ g = f ∘ h → g = h
def hasleftinv {A B : Type}(f : A → B) : Prop := ∃ (g : B → A), g ∘ f = id

theorem TIdInj : injective (@id A) := by
  -- we call out the definition
  rw [injective]
  intro a1 a2 h
  /-
  A : Type
  a1 a2 : A
  h : id a1 = id a2
  ⊢ a1 = a2
  -/
  calc  -- build a chain of calculation
    a1 = id a1 := by exact rfl
    _ = id a2 := by exact h
    _ = a2 := by exact rfl

theorem TIdMon : monomorphism (@id A) := by
  rw [monomorphism]
  intro C g h h2
  /-
  A C : Type
  g h : C → A
  h2 : id ∘ g = id ∘ h
  ⊢ g = h
  -/
  calc
    g = id g := by exact rfl
    _ = id ∘ h := by exact h2
    _ = h := by exact rfl

theorem TIdHasLeftInv : hasleftinv (@id A) := by
  rw [hasleftinv]
  apply Exists.intro id  -- which means sub g = id
  exact rfl

def surjective {A B : Type}(f : A → B): Prop := ∀ (y : B), ∃ (x : A), f x = y
def epimorphism {A B : Type} (f : A → B) : Prop := ∀{C : Type}, ∀{g h : B → C}, g ∘ f = h ∘ f → g = h
def hasrightinv {A B : Type}(f : A → B) : Prop := ∃(g : B → A), f ∘ g = id

theorem TIdSurj : surjective (@id A) := by
  rw [surjective]
  intro a
  apply Exists.intro a
  rfl

theorem TIdEpi : epimorphism (@id A) := by
  rw [epimorphism]
  intro B g h h1
  calc
    g = g ∘ id := by exact rfl
    _ = h ∘ id := by exact h1
    _ = h := by exact rfl

theorem TIdHasrightinv : hasrightinv (@id A) := by
  rw [hasrightinv]
  apply Exists.intro id
  rfl

def bijective {A B : Type} (f : A → B) : Prop := injective f ∧ surjective f
def isomorphism {A B : Type} (f : A → B) : Prop := ∃ (g : B → A), g ∘ f = id ∧ f ∘ g = id

theorem TidBij : bijective (@id A) := by
  rw [bijective]
  apply And.intro
  exact TIdInj
  exact TIdSurj

-- id is an isomorphism
theorem TIdIso : isomorphism (@id A) := by
  rw [isomorphism]
  apply Exists.intro id
  apply And.intro
  rfl
  rfl
