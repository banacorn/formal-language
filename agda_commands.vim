command! WC w<bar>call system("echo `pwd -P`/".expand('%')." | nc localhost 1531")
imap <C-g> <ESC>:WC<CR>
nmap <C-g> <ESC>:WC<CR>

imap <C-c> <ESC>:call Wrap_comment()<CR>
nmap <C-c> :call Wrap_comment()<CR>
vmap <C-c> :call Wrap_comment()<CR>

function! Wrap_comment ()
    let l:line = getline('.')

    if l:line[0:1] == '--'
        let l:line = l:line[2:]

    else
        let l:line = '--' . l:line
    endif

    call setline('.', l:line)
    execute "normal ^l"
    echom ""
endfunction
