# Lean Learning 

## Introduction 

This is a repository for documenting my learning process on **Lean**.

## Running Lean Project Template

1. Open Powershell
2. Switch to the directory of the template
    ```powershell
    cd "C:\Users\user\Desktop\digital_tools\Lean"
    ```
3. Run the template script and type the name of the new project
    ```powershell
    .\New-LeanMathlibProject.ps1 my_new_project
    ```
    If an error is returned, try 
    ```powershell
    Set-ExecutionPolicy -ExecutionPolicy Bypass -Scope Process
    ```
    and then run the previous command again.