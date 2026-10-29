import CLightLean.Cop

namespace Test.Exec

attribute [local instance] x86_64

def float32ComparisonsPass : Bool :=
  let x : CompCert.Float32 := 1.5
  let y : CompCert.Float32 := 2.25
  let nan : CompCert.Float32 := CompCert.Float32.default_nan
  CompCert.Float32.cmp .Ceq x y == false &&
    CompCert.Float32.cmp .Cne x y == true &&
    CompCert.Float32.cmp .Clt x y == true &&
    CompCert.Float32.cmp .Cle x y == true &&
    CompCert.Float32.cmp .Cgt x y == false &&
    CompCert.Float32.cmp .Cge x y == false &&
    CompCert.Float32.cmp .Ceq nan x == false &&
    CompCert.Float32.cmp .Cne nan x == true &&
    CompCert.Float32.cmp .Clt nan x == false &&
    CompCert.Float32.cmp .Cle nan x == false &&
    CompCert.Float32.cmp .Cgt nan x == false &&
    CompCert.Float32.cmp .Cge nan x == false

def float64ComparisonsPass : Bool :=
  let x : CompCert.Float64 := 1.5
  let y : CompCert.Float64 := 2.25
  let nan : CompCert.Float64 := CompCert.Float64.default_nan
  CompCert.Float64.cmp .Ceq x y == false &&
    CompCert.Float64.cmp .Cne x y == true &&
    CompCert.Float64.cmp .Clt x y == true &&
    CompCert.Float64.cmp .Cle x y == true &&
    CompCert.Float64.cmp .Cgt x y == false &&
    CompCert.Float64.cmp .Cge x y == false &&
    CompCert.Float64.cmp .Ceq nan x == false &&
    CompCert.Float64.cmp .Cne nan x == true &&
    CompCert.Float64.cmp .Clt nan x == false &&
    CompCert.Float64.cmp .Cle nan x == false &&
    CompCert.Float64.cmp .Cgt nan x == false &&
    CompCert.Float64.cmp .Cge nan x == false

def floatComparisonsPass : Bool :=
  float32ComparisonsPass && float64ComparisonsPass

#eval do
  if floatComparisonsPass then
    IO.println "float comparisons: pass"
  else
    throw (IO.userError "float comparisons: failed")

end Test.Exec
