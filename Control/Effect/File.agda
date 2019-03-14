
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

postulate
  FileHandle : Set

data IOMode : Set where
  readMode writeMode appendMode readWriteMode : IOMode

private variable m : IOMode

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

{-# COMPILE GHC FileHandle = type Handle #-}
{-# COMPILE GHC IOMode = data IOMode (ReadMode | WriteMode | AppendMode | ReadWriteMode) #-}
{-# COMPILE GHC IOError = data IOErrorType ( AlreadyExists | NoSuchThing | ResourceBusy | ResourceExhausted
                                           | EOF | IllegalOperation | PermissionDenied | UserError
                                           | UnsatisfiedConstraints | SystemError | ProtocolError | OtherError
                                           | InvalidArgument | InappropriateType | HardwareFault
                                           | UnsupportedOperation | TimeExpired | ResourceVanished | Interrupted )
 #-}

private
  postulate
    hClose   : FileHandle → IO ⊤
    hOpen    : String → IOMode → IO (Either IOError FileHandle)
    hGetLine : FileHandle → IO String

{-# FOREIGN GHC
  hOpen :: Text.Text -> IOMode -> IO (Either IOErrorType Handle)
  hOpen name mode =
    (Right <$> openFile (Text.unpack name) mode)
      `catch` \ e -> return (Left $ ioe_type e)
#-}

{-# COMPILE GHC hClose   = hClose #-}
{-# COMPILE GHC hOpen    = hOpen  #-}
{-# COMPILE GHC hGetLine = \ h -> Text.pack <$> hGetLine h #-}

data _openIn_ (h : FileHandle) (m : IOMode) : Set where
  evidence : h openIn m

data FileIOResult (A : Set) : Set where
  success : A → FileIOResult A
  failure : IOError → FileIOResult A

openFileResource : IOMode → FileIOResult FileHandle → Set
openFileResource m (success h) = h openIn m
openFileResource _ (failure _) = ⊤

data CanRead : IOMode → Set where
  instance
    readMode      : CanRead readMode
    readWriteMode : CanRead readWriteMode

data FileIO : Effect where
  openFile  : String → (m : IOMode) → FileIO (FileIOResult FileHandle) ⊤ (openFileResource m)
  closeFile : (h : FileHandle) → FileIO ⊤ (h openIn m) (λ _ → ⊤)
  getLine   : ⦃ c : CanRead m ⦄ (h : FileHandle) → FileIO String (h openIn m) (λ _ → h openIn m)

FILE : Set → EFFECT
FILE H = mkEff H FileIO

instance
  HandleFileIO : Handler FileIO IO
  HandleFileIO .handle r (openFile name m) k = do
    right h ← hOpen name m
      where left err → k (failure err) _
    k (success h) evidence
  HandleFileIO .handle _ (closeFile h) k = do
    hClose h
    k _ _
  HandleFileIO .handle r (getLine h) k = do
    s ← hGetLine h
    k s r
