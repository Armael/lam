### lam

#### alloc_stack

```
⟦alloc_stack (v ↦ eᵥ) (vₑ vₖ ↦ e_f)⟧ =
  λk. k (λf x k'. f x (λv. λ_. ⟦eᵥ⟧) (λvₑ vₖ. ⟦e_f⟧) k')
```

#### resume

```
⟦resume stack f v⟧ =
  λk.
    ⟦v⟧ (λv.
      ⟦f⟧ (λf.
        ⟦stack⟧ (λstack.
          stack f v k
        )
      )
    )
```

#### perform

```
⟦perform e⟧ =
  λk.
    ⟦e⟧ (λvₑ.
      λh_f. h_f e (λf x k'. f x k h_f k')
    )
```

#### delegate

```
⟦delegate e stack⟧ =
  λk.
    ⟦stack⟧ (λstack.
      ⟦e⟧ (λvₑ.
        λh_f. h_f vₑ stack
      )
    )
```

#### sugar

```
let continue stack e =
  resume stack (λx. x) e

let discontinue stack exn =
  resume stack (λx. raise x) exn

let handle body (v ↦ eᵥ) (vₑ vₖ ↦ e_f) =
  resume (alloc_stack (v ↦ eᵥ) (vₑ vₖ ↦ e_f)) (λ(). body) ()
```

--------

### with exceptions

#### alloc_stack

```
⟦alloc_stack (v ↦ eᵥ) (vₓ ↦ eₓ) (vₑ vₖ ↦ e_f)⟧ =
  λk. k (λf x k'. f x (λv. λ_ _. ⟦eᵥ⟧) (λvₓ. ⟦eₓ⟧) (λvₑ vₖ. ⟦e_f⟧) k')
```

#### resume

```
⟦resume stack f v⟧ =
  λk.
    ⟦v⟧ (λv.
      ⟦f⟧ (λf.
        ⟦stack⟧ (λstack.
          stack f v k
        )
      )
    )
```

#### perform

```
⟦perform e⟧ =
  λk.
    ⟦e⟧ (λvₑ.
      λhₓ h_f. h_f e (λf x k'. f x k hₓ h_f k')
    )
```

#### delegate

```
⟦delegate e stack⟧ =
  λk.
    ⟦stack⟧ (λstack.
      ⟦e⟧ (λvₑ.
        λhₓ h_f. h_f vₑ stack
      )
    )
```

#### raise

```
⟦raise e⟧ =
  λ k.
    ⟦e⟧ (λvₑ.
      λhₓ h_f. hₓ vₑ
    )
```
