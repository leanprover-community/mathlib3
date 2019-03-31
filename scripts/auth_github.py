from git import Repo, InvalidGitRepositoryError
from github import Github
import configparser

def auth_github():
    try:
        repo = Repo('.', search_parent_directories=True)
        config = repo.config_reader()
    except:
        print('This does not seem to be a git repository.')
        return Github()
    try:
        return Github(config.get('github', 'user'), config.get('github', 'password'))
    except configparser.NoSectionError:
        print('No github section found in \'git config\'')
        return Github()
    except configparser.NoOptionError:
        try:
            return Github(config.get('github', 'oauthtoken'))
        except configparser.NoOptionError:
            print('No github \'user\'/\'password\' or \'oauthtoken\' keys found in \'git config\'.')
            print('You can create an OAuth token at https://github.com/settings/tokens/new (no scopes are required).')
            return Github()