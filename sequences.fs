namespace LowDiscrepancySequences

open System
open System.Numerics

open sobolConstants

/// <summary>Low-discrepancy sequence definded by the additive recurrence.</summary>
type Additive 
    /// <summary>Initializes the <c>nDims</c>-dimensional sequence definded by the additive recurrence.</summary>
    /// <param name="nDims">The number of dimensions.</param>
    /// <returns>The <c>nDims</c>-dimensional sequence definded by the additive recurrence.</returns>
    /// <exception cref="System.ArgumentException">Thrown when <c>nDims</c> is less than 1 or greater than 8.</exception>
    (nDims : int) = 

    do if nDims < 1 then 
        invalidArg "nDims" "Sequence dimension must be positive."

    let nDimsMax = 176

    do if nDims > nDimsMax then 
        invalidArg "nDims" <| sprintf "Sequence dimension must be at most %i." nDimsMax

    let phi i = 
        let d = float i + 1.0
        let mutable phi = 2.0
        let mutable phi2 = (phi + 1.0) ** (1.0 / (d + 1.0))

        while phi <> phi2 do
            phi <- phi2
            phi2 <- (phi + 1.0) ** (1.0 / (d + 1.0))
        phi

    let phis = Array.init nDims phi

    let u = Array.create nDims 0.0

    /// <summary>The number of dimensions <c>nDims</c>.</summary>
    member this.NDims = nDims

    /// <summary>Calculates the next point in the sequence.</summary>
    /// <returns>The next point in the sequence.</returns>
    member this.Next () = 
        for i in 0 .. nDims - 1 do 
            u[i] <- (u[i] + phis[i]) % 1.0
        Array.copy u

/// <summary>Low-discrepancy Halton sequence.</summary>
type Halton 
    /// <summary>Initializes the <c>nDims</c>-dimensional Halton sequence.</summary>
    /// <param name="nDims">The number of dimensions.</param>
    /// <returns>The <c>nDims</c>-dimensional Halton sequence.</returns>
    /// <exception cref="System.ArgumentException">Thrown when <c>nDims</c> is less than 1 or greater than 8.</exception>
    (nDims : int) = 

    do if nDims < 1 then invalidArg "dim" "Sequence dimension must be positive."

    let primes = [|2; 3; 5; 7; 11; 13; 17; 19|]
    let nDimsMax = Array.length primes

    do if nDims > nDimsMax then invalidArg "nDims" <| sprintf "Sequence dimension must be at most %i." nDimsMax

    let bases = Array.take nDims primes

    let n = Array.create nDims 0
    let d = Array.create nDims 1
    let x = Array.create nDims 0
    let y = Array.create nDims 0

    let u = Array.create nDims 0.0

    /// <summary>The number of dimensions <c>nDims</c>.</summary>
    member this.NDims = nDims

    /// <summary>Calculates the next point in the sequence.</summary>
    /// <returns>The next point in the sequence.</returns>
    member this.Next () = 
        for i in 0 .. nDims - 1 do
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

/// <summary>Low-discrepancy Sobol sequence.</summary>
type Sobol 
    /// <summary>Initializes the <c>nDims</c>-dimensional Sobol sequence.</summary>
    /// <param name="nDims">The number of dimensions.</param>
    /// <returns>The <c>nDims</c>-dimensional Sobol sequence.</returns>
    /// <exception cref="System.ArgumentException">Thrown when <c>nDims</c> is less than 1 or greater than 21200.</exception>
    (nDims : int) = 

    do if nDims < 1 then invalidArg "nDims" "Sequence dimension must be positive."

    let nDimsMax = Array.length aSobol

    do printfn "%A" nDimsMax

    do if nDims > nDimsMax then invalidArg "nDims" <| sprintf "Sequence dimension must be at most %i." nDimsMax

    let m = Array2D.create nDims 32 1u
    let x = Array.create nDims 0u
    let b = Array.create nDims 0u
    let mutable n = 0u

    let mutable cTemp = 0u
    let mutable bTemp = 0u

    let u = Array.create nDims 0.0

    let sysRand = System.Random 0 // in case we run out of elements

    let bitCastInt32 (a : uint32) : int32 = a |> BitConverter.GetBytes |> BitConverter.ToInt32

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

    /// <summary>The number of dimensions <c>nDims</c>.</summary>
    member this.NDims = nDims

    /// <summary>Calculates the next point in the sequence.</summary>
    /// <returns>The next point in the sequence.</returns>
    member this.Next () = 
        if n = 0u - 1u then
            eprintf "Maximum number of points in the Sobol sequence reached. "
            eprintfn "Returning a pseudorandom point."

            for i in 0 .. nDims - 1 do
                u[i] <- sysRand.NextDouble ()
        else 
            n <- n + 1u

            cTemp <- BitOperations.TrailingZeroCount n |> uint
            for i in 0 .. nDims - 1 do
                bTemp <- b[i]
                if bTemp >= cTemp then
                    x[i] <- x[i] ^^^ (m[i, int cTemp] <<< int (bTemp - cTemp))
                    u[i] <- float x[i] * 2.0 ** float (bitCastInt32 ~~~bTemp)
                else
                    x[i] <- (x[i] <<< int (cTemp - bTemp)) ^^^ m[i, int cTemp]
                    b[i] <- cTemp
                    u[i] <- float x[i] * 2.0 ** float (bitCastInt32 ~~~cTemp)
        Array.copy u
