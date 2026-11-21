import P256.Proofs.Verifying.Combination.Table.Site
import P256.Proofs.Verifying.Combination.Table.Setup

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Table

def addSite1 : AddSite :=
  ⟨0xb06e, by decide, by decide +kernel,
    ⟨0xb074, 0xffffa177, by decide, by decide +kernel, by decide +kernel⟩, rfl⟩

def addSite2 : AddSite :=
  ⟨0xb089, by decide, by decide +kernel,
    ⟨0xb08f, 0xffffa15c, by decide, by decide +kernel, by decide +kernel⟩, rfl⟩

def addSite3 : AddSite :=
  ⟨0xb0a7, by decide, by decide +kernel,
    ⟨0xb0ad, 0xffffa13e, by decide, by decide +kernel, by decide +kernel⟩, rfl⟩

def addSite4 : AddSite :=
  ⟨0xb0c5, by decide, by decide +kernel,
    ⟨0xb0cb, 0xffffa120, by decide, by decide +kernel, by decide +kernel⟩, rfl⟩

def addSite5 : AddSite :=
  ⟨0xb0e3, by decide, by decide +kernel,
    ⟨0xb0e9, 0xffffa102, by decide, by decide +kernel, by decide +kernel⟩, rfl⟩

def addSite6 : AddSite :=
  ⟨0xb101, by decide, by decide +kernel,
    ⟨0xb107, 0xffffa0e4, by decide, by decide +kernel, by decide +kernel⟩, rfl⟩

def addSite7 : AddSite :=
  ⟨0xb11f, by decide, by decide +kernel,
    ⟨0xb125, 0xffffa0c6, by decide, by decide +kernel, by decide +kernel⟩, rfl⟩

def addSite8 : AddSite :=
  ⟨0xb13d, by decide, by decide +kernel,
    ⟨0xb143, 0xffffa0a8, by decide, by decide +kernel, by decide +kernel⟩, rfl⟩

def copySite1 : CopySite 1 :=
  ⟨0xb079, tableCopySetup1Bytes, by decide, by decide +kernel,
    0xb086, by decide, by decide +kernel, tableCopySetup1_correct⟩

def copySite2 : CopySite 2 :=
  ⟨0xb094, tableCopySetup2Bytes, by decide, by decide +kernel,
    0xb0a4, by decide, by decide +kernel, tableCopySetup2_correct⟩

def copySite3 : CopySite 3 :=
  ⟨0xb0b2, tableCopySetup3Bytes, by decide, by decide +kernel,
    0xb0c2, by decide, by decide +kernel, tableCopySetup3_correct⟩

def copySite4 : CopySite 4 :=
  ⟨0xb0d0, tableCopySetup4Bytes, by decide, by decide +kernel,
    0xb0e0, by decide, by decide +kernel, tableCopySetup4_correct⟩

def copySite5 : CopySite 5 :=
  ⟨0xb0ee, tableCopySetup5Bytes, by decide, by decide +kernel,
    0xb0fe, by decide, by decide +kernel, tableCopySetup5_correct⟩

def copySite6 : CopySite 6 :=
  ⟨0xb10c, tableCopySetup6Bytes, by decide, by decide +kernel,
    0xb11c, by decide, by decide +kernel, tableCopySetup6_correct⟩

def copySite7 : CopySite 7 :=
  ⟨0xb12a, tableCopySetup7Bytes, by decide, by decide +kernel,
    0xb13a, by decide, by decide +kernel, tableCopySetup7_correct⟩

end P256.Proofs.Verifying.Combination.Table
