let _ =
  CmdLineParser.parse_cmdline [
      ("aes_key_expansion", "0",   X64_AES128.va_code_KeyExpansion128Stdcall);
      ("gcm_encrypt",       "100", X64_GCMencrypt.va_code_gcm_encrypt_stdcall);
      ("gcm_decrypt",       "200", X64_GCMdecrypt.va_code_gcm_decrypt_stdcall)
    ]
