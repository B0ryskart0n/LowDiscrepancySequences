module LowDiscrepancySequences

open System
open System.IO
open System.Numerics
// add ndims method

type Additive (dim: int) = 
    do if dim < 1 then invalidArg "dim" "Sequence dimension must be positive."

    let primes = [|2.0; 3.0; 5.0; 7.0; 11.0; 13.0; 17.0; 19.0|]

    let dimMax = Array.length primes
    do if dim > dimMax then invalidArg "dim" <| sprintf "Sequence dimension must be at most %i." dimMax

    let bases = 
        match dim with
        | 1 -> [|(sqrt 5.0 - 1.0) / 2.0|] // golden ratio
        | _ -> 
            primes
            |> Array.take dim
            |> Array.map sqrt
            |> Array.map (fun x -> x % 1.0) // this is not needed but may be faster (to be checked)

    let u = Array.create dim 0.0

    member this.Next () =
        for i in 0..dim-1 do
            u[i] <- (u[i] + bases[i]) % 1.0
        Array.copy u

    member this.NextFast () =
        for i in 0..dim-1 do
            u[i] <- (u[i] + bases[i]) % 1.0
        u

// maybe write default (bases: list<int>) and new (dim: int) = Halton (Array.take dim primes)
type Halton (dim: int) = 
    do if dim < 1 then invalidArg "dim" "Sequence dimension must be positive."

    let primes = [|2; 3; 5; 7; 11; 13; 17; 19|]

    let dimMax = Array.length primes
    do if dim > dimMax then invalidArg "dim" <| sprintf "Sequence dimension must be at most %i." dimMax

    let bases = Array.take dim primes

    let n = Array.create dim 0
    let d = Array.create dim 1
    let x = Array.create dim 0
    let y = Array.create dim 0

    let u = Array.create dim 0.0

    member this.Next () = 
        for i in 0..dim-1 do
            x[i] <- d[i] - n[i]

            if x[i] = 1 then 
                n[i] <- 1
                d[i] <- d[i] * bases[i]
            else 
                y[i] <- d[i] / bases[i]
                while x[i] <= y[i] do 
                    y[i] <- y[i] / bases[i]
                n[i] <- (bases[i] + 1) * y[i] - x[i]
            u[i] <- float n[i] / float d[i]
        Array.copy u

    member this.NextFast () = 
        for i in 0..dim-1 do
            x[i] <- d[i] - n[i]

            if x[i] = 1 then 
                n[i] <- 1
                d[i] <- d[i] * bases[i]
            else 
                y[i] <- d[i] / bases[i]
                while x[i] <= y[i] do 
                    y[i] <- y[i] / bases[i]
                n[i] <- (bases[i] + 1) * y[i] - x[i]
            u[i] <- float n[i] / float d[i]
        u
    
    member this.Current () = Array.copy u

    member this.CurrentFast () = u

module Constats = 
    let aSobol = 
        File.ReadAllLines "aSobol.txt" 
        |> Array.map uint

    let minitSobol = 
        File.ReadAllLines "minitSobol.txt"
        |> Array.map (fun s -> s.Split [|','|])
        |> array2D
        |> Array2D.map uint
open Constats

type Sobol (nDims: int) = 
    do if nDims < 1 then invalidArg "nDims" "Sequence dimension must be positive."

    let nDimsMax = Array.length aSobol
    do if nDims > nDimsMax then invalidArg "nDims" <| sprintf "Sequence dimension must be at most %i." nDimsMax

    let m = Array2D.create nDims 32 1u
    let x = Array.create nDims 0u
    let b = Array.create nDims 0u
    let mutable n = 0u

    let mutable cTemp = 0u
    let mutable bTemp = 0u

    let u = Array.create nDims 0.0

    do if nDims > 1 then
        let mutable a = 0u
        let mutable d = 0

        let mutable ac = a

        for i in 1 .. nDims - 1 do
            a <- aSobol[i - 1]
            d <- (a |> float |> log) / (log 2.0) |> int32

            m[i, 0 .. d - 1] <- minitSobol[0 .. d - 1, i - 1]
            for j in d .. 31 do
                ac <- a
                
                m[i, j] <- m[i, j - d]
                for k in 0 .. d - 1 do 
                    m[i, j] <- m[i, j] ^^^ (((ac &&& 1u) * m[i, j - d + k]) <<< (d - k))
                    ac <- ac >>> 1

    let bitCastInt32 (a: uint32) = a |> BitConverter.GetBytes |> BitConverter.ToInt32

    member this.CalculateNext () = 
        if n = 0u - 1u then failwith "Maximum number of points in the Sobol sequence already reached."

        n <- n + 1u

        cTemp <- BitOperations.TrailingZeroCount n |> uint
        for i in 0 .. nDims - 1 do
            bTemp <- b[i]
            if bTemp >= cTemp then
                x[i] <- x[i] ^^^ (m[i, int cTemp] <<< int (bTemp - cTemp))
                u[i] <- float x[i] * 2.0 ** float (bitCastInt32 ~~~bTemp) // should be ldexp (C.math.ldexp)
            else
                x[i] <- (x[i] <<< int (cTemp - bTemp)) ^^^ m[i, int cTemp]
                b[i] <- cTemp
                u[i] <- float x[i] * 2.0 ** float (bitCastInt32 ~~~cTemp) // should be ldexp (C.math.ldexp)

    member this.Next () = 
        this.CalculateNext () // |> ignore
        Array.copy u
    
    member this.NextFast () = 
        this.CalculateNext () // |> ignore
        u