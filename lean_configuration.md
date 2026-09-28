# Lean

Any detail about Lean can be found on [github-lean community](https://leanprover-community.github.io/), [lean community website](https://leanprover-community.github.io/index.html).

The AI model `deepseek-V4.1-Flash` assisted with the whole process.

# Configuration

The complete enviroment of Lean requires following components:
- **VS code**
- **git**
- **elan**: version manager of Lean
- **lake**: (Lean Make) a new build system and package manager for Lean 4. Users need lake to compile a lean document.
- **Lean**

## VS code and git

One needs **visual studio code** and **git** before anything.
- [VS code](https://code.visualstudio.com/) 
- [git](https://git-scm.com/install/windows)

VS code provides an extension about Lean. Users can directly download it by searching **Lean 4** extension.

## elan

Download by Powershell:
```powershell
Invoke-WebRequest -Uri "https://elan.lean-lang.org/elan-init.ps1" -OutFile "elan-init.ps1"
powershell -ExecutionPolicy Bypass -f elan-init.ps1
```
- `Invoke-WebRequest` 是 PowerShell 原生的命令，用來發送 HTTP 請求。
- `-Uri` 指定要訪問的網址。
- `-OutFile` 指定把服務器返回的內容保存到哪個本地文件。
- `powershell`：啟動一個新的 Windows PowerShell 進程；
- `-ExecutionPolicy Bypass`：告訴這個新進程，臨時把腳本執行策略設爲 Bypass，也就是允許運行腳本；
- `-f elan-init.ps1`：`-f` 是 -File 的縮冩，表示運行指定的腳本文件。這會啟動一個子 PowerShell，並在裡面運行剛剛下載好的 `elan-init.ps1`。

One can see the version of **elan** by 
```powershell
elan --version
```

## lake and lean
**Lake** is downloaded with **elan** . It is a part of the toolchain of Lean 4. The toolchain, lake and lean can be seen by 
```powershell
elan toolchain list
lake --version
lean --version
```

## Mathlib4

**Lean Mathematical Library for Lean 4** is a preprocessed mathematical library for Lean 4. Users can directly call mathematical contents from Mathlib4, instead of defining them again.

### Download
1. Choose a path in your device for placing the folder of **Mathlib4**.
2. Open powershell and run
```powershell
git clone https://github.com/leanprover-community/mathlib4.git
cd mathlib4   # A new document called "mathlib4" is added
lake exe cache get
```
`lake exe cache get` downloads the precompiled `.olean` cache for Mathlib to avoid recompiling from source.

### Update version
Updating the version of **Mathlib** that downloaded locally:
1. Enter the directory of **Mathlib**
2. Pull the newest version from github
    ```powershell
    git pull origin master
    ```
3. Update **Lean** toolchain
    ```powershell
    curl.exe -L https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
    ```
    This command downloads the newest version of **mathlib** from the official repository and overwrite the local version.
4. Update the dependency
    ```powershell
    lake update
    lake exe cache get
    ```

### Invoking Mathlib4
The users can import Mathlib4 by typing the following in the beginning of a lean document
```lean
import Mathlib
```
One can only import a particular part of Mathlib4 by
```lean
import Mathlib. ...
```

## Project
A folder managed by **lake**, including configuration files, dependency, and raw codes, so that **lake** knows how to compile the project, which version of Lean to use, and which packages to load.

### Documents in a project folder

If one creates a new project(name `beginning` here) by vs code, then a folder with the following structure is generated
```bash
├── .github/
├── .lake/ 
├── Beginning/ 
├── .gitignore 
├── Beginning.lean
├── lake-manifest.json
├── lakefile.toml
├── lean-toolchain
├── Main.lean 
└── README.md
```
- `lakefile.toml`: The configuration file of the project. *Lake* uses it to determine the project name, dependencies, and the libraries or executables to be built.
- `lean-toolchain`: Specify the Lean version to be used for this project.
- `Beginning.lean`: Main document of the project.
- `Main.lean`: The entry-point file of the executive document(`.exe`) if necessary. Usually involve `def main`.
- `lake-manifest.json`: Automatically generated. It records the versions and paths of the dependencies actually downloaded.
- `.lake/`: Automatically generated. It stores build artifacts and dependency caches.
- `.gitignore`: It tells git which files not to track.
- `Beginning/`: If a library contains multiple modules, a folder with the same name as the library is typically used to house the multiple `.lean` files.(Capitalization of the first letter is automatic due to syntax)

Only `lakefile.toml`, `lean-toolchain` and `*.lean` are necessary for a project. Thus, the minimum structure of a project is
```bash
my_project/
├── lakefile.toml
├── lean-toolchain
└── MyProject.lean
```

### Building a new project

- by Powershell:

    Choose a place that you want to build the project, then
    ```powershell
    cd path
    lake new project_name
    cd project_name
    code .
    ```

- by VS code:
(Assume that Lean extension and mathlib is downloaded)

    1. Open a folder that you want to build the project
    2. Click *Lean 4 symbol* in the top-right corner. 
    3. Click *New Project*.
       1. *Standalone Project*: a simple lean project
       2. *project using mathlib*: a project containing mathlib, but it need a long time to download mathlib

### Invoking local mathlib4 for new project
1. Create *Standalone Project* in a particular path. 
2. Edit `lakefile.toml` and add the following in the end
    ```toml
    [[require]]
    name = "mathlib"
    path = "C:/..."
    ```
    The path here is that of the folder of mathlib4 downloaded locally. Note that one should use forwar slash `/` instead of blackslash `\`. 
3. Make sure that the version of mathlib4 downloaded is same to that in the project. One can find the version of the project by the document `lean-toolchain` in the project folder.
4. Open powershell and shift to the folder of the project. Rebuild the dependency and compile:
    ```powershell
    del lake-manifest.json
    lake update
    lake build
    ```
    - `del lake-manifest.json`: delete the previous dependency documents.
    - `lake update`: read `lakefile.toml`，and connect the local mathlib4
    - `lake build`: compile

    Type `import Mathlib` in `.lean` document. If no any error, then the local mathlib4 is successfully invoked.

### Update the version of Mathlib
If the version **mathlib** that a project used updates, then the following needed to be executed:
1. Checking the current version of mathlib
    ```powershell
    type C:\Users\...\mathlib4\lean-toolchain
    ```
    the path here refers to the local mathlib
2. Enter the project and change `lean-toolchain` to match mathlib
    ```powershell
    cd C:\Users\...\project
    Copy-Item C:\Users\...\mathlib4\lean-toolchain .\lean-toolchain -Force
    ```
    `Copy-Item C:\...` is the path of local mathlib4
3. Clean up old build artifacts
    ```powershell
    Remove-Item -Recurse -Force .lake
    Remove-Item -Force lake-manifest.json
    ```
4. Compile and build again
    ```powershell
    lake update
    lake exe cache get
    lake build
    ```

## Delete a Project
When a Lean project is opened in VS code, Lean 4 extension launches the Lean and Lake processes in the background so that user sometimes cannot delete the project directly. In detail, `.lake` folder cannot be deleted directly. 

Users can delete it after turning off VS code. Or:

1. Run `powershell` as administrator.
2. Switch to the directory of the project
3. Execute
    ```powershell
    Remove-Item -Recurse -Force .lake
    ```

## Invoking and Managing Lean Version 

### Downloading a Lean Version
```powershell
elan toolchain install leanprover/lean4:v...
```
where `v...` is the version, such as `v4.30.0`. This command downloads a Lean toolchain of the specified version in a path like
```bash
C:\Users\user\.elan\toolchains\leanprover--lean4---v4.30.0\
```
so that user have a complete Lean environment of that version.

Users can view the environment downloaded by
```powershell
elan toolchain list
```
For a project, users can view the current environment by
```powershell
cd path_of_project
elan show
```

### Default Version Invoked
```powershell
elan default leanprover/lean4:v...
```
This command set the specified version of Lean as the default one.

Users can view the current default version by
```powershell
elan default
```

### Changing Version of a Project

Users can change the version of a project by editinig `lean-toolchain`
```lean-toolchain
leanprover/lean4:v...
```
and then
```powershell
lake update
lake exe cache get
lake build
```
in order to update the building artifacts. Note that the path of mathlib4 in `lakefile.toml` should be aligned with the path of the new version.


## Importing a particular library of Mathlib

| Fields of Math | Corresponding `import` |
| --- | --- |
| Basic tactic(ring、linarith、omega、simp) | `import Mathlib.Tactic` |
| National numbers, integers | `import Mathlib.Data.Nat.Basic`, `import Mathlib.Data.Int.Basic` |
| Real numbers | `import Mathlib.Data.Real.Basic` |
| Rational numbers | `import Mathlib.Data.Rat.Basic` |
| Complex numbers | `import Mathlib.Data.Complex.Basic` |
| Sets | `import Mathlib.Data.Set.Basic` |
| Groups, rings | `import Mathlib.Algebra.Group.Basic`, `import Mathlib.Algebra.Ring.Basic` |
| Linear Algebra | `import Mathlib.LinearAlgebra.Basic` |
| Topology | `import Mathlib.Topology.Basic` |
| Analysis, Calculus | `import Mathlib.Analysis.Calculus.Deriv.Basic` |
| Measure, Integrals | `import Mathlib.MeasureTheory.Integral.Bochner` |