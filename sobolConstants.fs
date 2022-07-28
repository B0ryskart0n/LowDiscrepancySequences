namespace LowDiscrepancySequences

open System.IO

module internal sobolConstants =
    let aSobol = 
        File.ReadAllLines "aSobol.txt" 
        |> Array.map uint

    let minitSobol = 
        File.ReadAllLines "minitSobol.txt"
        |> Array.map (fun s -> s.Split [|','|])
        |> array2D
        |> Array2D.map uint
