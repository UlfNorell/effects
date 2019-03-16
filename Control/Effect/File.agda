
module Control.Effect.File where

open import Prelude
open import Container.List
open import Control.Effect
open import Variables
open import Lib

{-# FOREIGN GHC import System.IO #-}
{-# FOREIGN GHC import GHC.IO.Exception (IOErrorType(..), ioe_type) #-}
{-# FOREIGN GHC import Control.Exception #-}
{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}

postulate
  RawHandle : Set

data IOMode : Set where
  readMode writeMode appendMode readWriteMode : IOMode

private
  module FH where
    record FileHandle (m : IOMode) : Set where
      no-eta-equality
      constructor fileHandle
      field rawHandle : RawHandle

open FH
open FH public using (FileHandle) hiding (module FileHandle)
open FileHandle

private variable mode : IOMode

data IOError : Set where
  eAlreadyExists
   eNoSuchThing
   eResourceBusy
   eResourceExhausted
   eEOF
   eIllegalOperation
   ePermissionDenied
   eUserError
   eUnsatisfiedConstraints
   eSystemError
   eProtocolError
   eOtherError
   eInvalidArgument
   eInappropriateType
   eHardwareFault
   eUnsupportedOperation
   eTimeExpired
   eResourceVanished
   eInterrupted : IOError

{-# COMPILE GHC RawHandle = type Handle #-}
{-# COMPILE GHC IOMode = data IOMode (ReadMode | WriteMode | AppendMode | ReadWriteMode) #-}
{-# COMPILE GHC IOError = data IOErrorType ( AlreadyExists | NoSuchThing | ResourceBusy | ResourceExhausted
                                           | EOF | IllegalOperation | PermissionDenied | UserError
                                           | UnsatisfiedConstraints | SystemError | ProtocolError | OtherError
                                           | InvalidArgument | InappropriateType | HardwareFault
                                           | UnsupportedOperation | TimeExpired | ResourceVanished | Interrupted )
 #-}

record Open (h : FileHandle mode) : Set where
record Closed : Set where

data FileIOResult (A : Set) : Set where
  success : A → FileIOResult A
  failure : IOError → FileIOResult A

openFileResource : (m : IOMode) → FileIOResult (FileHandle m) → Set
openFileResource m (success h) = Open h
openFileResource _ (failure _) = Closed

data CanRead : IOMode → Set where
  instance
    readMode      : CanRead readMode
    readWriteMode : CanRead readWriteMode

data CanWrite : IOMode → Set where
  instance
    writeMode     : CanWrite writeMode
    appendMode    : CanWrite appendMode
    readWriteMode : CanWrite readWriteMode

data FileIO : Effect where
  openFile   : String → (m : IOMode) →
               FileIO (FileIOResult (FileHandle m)) [ Closed => r ∙ openFileResource m r ]
  closeFile  : (h : FileHandle mode) → FileIO ⊤ [ Open h => Closed ]
  fReadLine  : ⦃ c : CanRead mode ⦄ (h : FileHandle mode) → FileIO String [- Open h -]
  fWriteLine : ⦃ w : CanWrite mode ⦄ (h : FileHandle mode) → String → FileIO ⊤ [- Open h -]

FILE : Set → List EFFECT
FILE H = [ FileIO ⊢ H ]

private
  postulate
    hClose    : RawHandle → IO ⊤
    hOpen     : String → IOMode → IO (Either IOError RawHandle)
    hGetLine  : RawHandle → IO String
    hPutStrLn : RawHandle → String → IO ⊤

{-# FOREIGN GHC
  hOpen :: Text.Text -> IOMode -> IO (Either IOErrorType Handle)
  hOpen name mode =
    (Right <$> openFile (Text.unpack name) mode)
      `catch` \ e -> return (Left $ ioe_type e)
  #-}

{-# COMPILE GHC hClose    = hClose #-}
{-# COMPILE GHC hOpen     = hOpen  #-}
{-# COMPILE GHC hGetLine  = Text.hGetLine #-}
{-# COMPILE GHC hPutStrLn = Text.hPutStrLn  #-}

instance
  HandleFileIO : Handler FileIO IO
  HandleFileIO .handle r (openFile name m) k = do
    right h ← hOpen name m
      where left err → k (failure err) _
    k (success $ fileHandle h) _
  HandleFileIO .handle _ (closeFile h) k = do
    hClose (rawHandle h)
    k _ _
  HandleFileIO .handle r (fReadLine h) k = do
    s ← hGetLine (rawHandle h)
    k s r
  HandleFileIO .handle r (fWriteLine h s) k = do
    hPutStrLn (rawHandle h) s
    k _ r
